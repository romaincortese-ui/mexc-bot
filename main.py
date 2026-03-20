"""
MEXC Trading Bot — 3 Strategies
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER  — 95% balance | TP +2%  | SL -1.5% | high-vol pairs | momentum
  2. MOONSHOT —  5% balance | TP +25% | SL -10%  | low-cap gems   | breakout
  3. REVERSAL —  5% balance | TP +3%  | SL -2%   | any volume     | oversold bounce
     Moonshot and Reversal share the 5% slot — whichever fires first wins.
     Moonshot auto-exits after 48h. Reversal auto-exits after 4h.

SETUP: Fill in your MEXC API details below. Leave PAPER_TRADE = True to start.
"""

import time, hmac, hashlib, logging, requests
import pandas as pd
import numpy as np
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG — edit these values before running
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = "mx0vglg1LIlEl98JhQ"
MEXC_API_SECRET = "2b53b21288c8494bbec5e0cc7f34d8c2"

PAPER_TRADE   = False    # ← keep True until ready for real money
PAPER_BALANCE = 50.0    # simulated starting balance

# ── Scalper (main strategy — momentum) ────────────────────────
SCALPER_BUDGET_PCT  = 0.95    # 95% of available balance
SCALPER_TP          = 0.020   # +2.0%
SCALPER_SL          = 0.015   # -1.5%
SCALPER_MIN_VOL     = 500_000 # min 24h USDT volume
SCALPER_THRESHOLD   = 20      # min signal score to enter
SCALPER_MAX_RSI     = 70      # don't enter overbought pairs

# ── Moonshot (breakout — low-cap gems) ────────────────────────
MOONSHOT_BUDGET_PCT = 0.05    # 5% of available balance
MOONSHOT_TP         = 0.25    # +25%
MOONSHOT_SL         = 0.10    # -10%
MOONSHOT_MAX_VOL    = 200_000 # max 24h volume (keeps it low-cap)
MOONSHOT_MIN_VOL    = 10_000  # min volume (avoid ghost coins)
MOONSHOT_THRESHOLD  = 25      # min signal score
MOONSHOT_MAX_HOURS  = 48      # exit after 48h regardless

# ── Reversal (mean reversion — oversold bounce) ────────────────
# Shares the 5% slot with moonshot — only one fires at a time
REVERSAL_TP         = 0.030   # +3%
REVERSAL_SL         = 0.020   # -2%
REVERSAL_MIN_VOL    = 100_000 # needs some liquidity
REVERSAL_MAX_RSI    = 32      # only enter deeply oversold pairs
REVERSAL_MIN_DROP   = 3.0     # pair must be down at least 3% in 24h
REVERSAL_MAX_HOURS  = 4       # exit after 4h regardless — bounce or bail

# ── Shared ────────────────────────────────────────────────────
MIN_PRICE     = 0.001   # ignore coins below this price (lot size quirks)
SCAN_INTERVAL = 60      # seconds between scans when idle

TELEGRAM_TOKEN   = "8729639207:AAGR2ytuX36ocCVagQj-tGBE2QEkvrTiqQo"
TELEGRAM_CHAT_ID = "7058246374"

# ═══════════════════════════════════════════════════════════════
#  END OF CONFIG
# ═══════════════════════════════════════════════════════════════

BASE_URL = "https://api.mexc.com"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler()]
)
log = logging.getLogger(__name__)

# ── State ──────────────────────────────────────────────────────
trade_history      = []
scalper_trade      = None
alt_trade          = None   # holds either a MOONSHOT or REVERSAL trade
last_heartbeat_at  = 0
last_daily_summary = ""
last_top_scalper   = None
last_top_alt       = None

# Exchange info cached once at startup
_exchange_info_cache   = {}
_exchange_info_fetched = False

# ── Telegram ───────────────────────────────────────────────────

def telegram(msg: str):
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
            json={"chat_id": TELEGRAM_CHAT_ID, "text": msg, "parse_mode": "HTML"},
            timeout=8,
        )
    except Exception as e:
        log.warning(f"Telegram send failed: {e}")

# ── MEXC API helpers ───────────────────────────────────────────

def public_get(path, params=None):
    r = requests.get(BASE_URL + path, params=params or {}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_get(path, params=None):
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    query  = "&".join(f"{k}={v}" for k, v in params.items())
    params["signature"] = hmac.new(
        MEXC_API_SECRET.encode(), query.encode(), hashlib.sha256
    ).hexdigest()
    r = requests.get(BASE_URL + path, params=params,
                     headers={"X-MEXC-APIKEY": MEXC_API_KEY}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_post(path, params=None):
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    query  = "&".join(f"{k}={v}" for k, v in params.items())
    params["signature"] = hmac.new(
        MEXC_API_SECRET.encode(), query.encode(), hashlib.sha256
    ).hexdigest()
    r = requests.post(BASE_URL + path, params=params,
                      headers={"X-MEXC-APIKEY": MEXC_API_KEY}, timeout=10)
    r.raise_for_status()
    return r.json()

# ── Exchange info cache ────────────────────────────────────────

def _load_exchange_info():
    global _exchange_info_fetched
    if _exchange_info_fetched:
        return
    log.info("📋 Loading exchange info (one-time)...")
    try:
        info = public_get("/api/v3/exchangeInfo")
        for s in info.get("symbols", []):
            sym  = s["symbol"]
            step, min_qty, min_notional = 0.001, 0.001, 1.0
            for f in s.get("filters", []):
                if f["filterType"] == "LOT_SIZE":
                    step    = float(f.get("stepSize", 0.001))
                    min_qty = float(f.get("minQty",   0.001))
                if f["filterType"] == "MIN_NOTIONAL":
                    min_notional = float(f.get("minNotional", 1.0))
            _exchange_info_cache[sym] = {"step": step, "min_qty": min_qty, "min_notional": min_notional}
        _exchange_info_fetched = True
        log.info(f"📋 Loaded rules for {len(_exchange_info_cache)} symbols.")
    except Exception as e:
        log.error(f"Failed to load exchange info: {e}")

def get_symbol_rules(symbol):
    rules = _exchange_info_cache.get(symbol)
    if rules:
        return rules["step"], rules["min_qty"], rules["min_notional"]
    return 0.001, 0.001, 1.0

# ── Balance ────────────────────────────────────────────────────

def get_available_balance() -> float:
    if PAPER_TRADE:
        pnl = sum(t["pnl_usdt"] for t in trade_history)
        return round(PAPER_BALANCE + pnl, 2)
    try:
        data = private_get("/api/v3/account")
        for b in data.get("balances", []):
            if b["asset"] == "USDT":
                return float(b["free"])
        log.warning("USDT balance not found.")
        return 0.0
    except Exception as e:
        log.error(f"Failed to fetch balance: {e}")
        return 0.0

# ── Quantity rounding ──────────────────────────────────────────

def round_qty(qty: float, step: float) -> float:
    """Floor qty to nearest valid step using integer arithmetic to avoid float artifacts."""
    if step <= 0:
        return qty
    decimals = max(0, -int(np.floor(np.log10(step)))) if step < 1 else 0
    factor   = 10 ** decimals
    return int(qty * factor // (step * factor)) * step / factor

# ── Indicators ─────────────────────────────────────────────────

def calc_rsi(series, period=14) -> float:
    delta = series.diff()
    gain  = delta.clip(lower=0).rolling(period).mean()
    loss  = (-delta.clip(upper=0)).rolling(period).mean()
    rs    = gain / loss.replace(0, np.nan)
    val   = (100 - (100 / (1 + rs))).iloc[-1]
    return float(val) if not np.isnan(val) else float("nan")

def calc_ema(series, span) -> pd.Series:
    return series.ewm(span=span, adjust=False).mean()

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
    """Fetch and parse klines robustly regardless of MEXC column count."""
    try:
        data = public_get("/api/v3/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        if not data:
            return None
        df = pd.DataFrame(data)
        df.columns = range(len(df.columns))
        df = df.rename(columns={0: "open_time", 1: "open", 2: "high", 3: "low", 4: "close", 5: "volume"})
        for col in ["open", "high", "low", "close", "volume"]:
            df[col] = pd.to_numeric(df[col], errors="coerce")
        df = df.dropna(subset=["close", "volume"])
        return df if len(df) >= min_len else None
    except Exception as e:
        log.info(f"⚠️ Klines error {symbol}: {type(e).__name__}: {e}")
        return None

# ── Pair scoring (shared signal engine) ───────────────────────

def score_pair(symbol, interval="5m") -> dict | None:
    df = parse_klines(symbol, interval)
    if df is None:
        return None
    try:
        close  = df["close"]
        volume = df["volume"]

        r = calc_rsi(close)
        if np.isnan(r):
            return None

        # RSI score: reward oversold (low RSI), penalise overbought (high RSI)
        rsi_score = max(0, 40 - r) if r < 50 else 0

        # EMA crossover score
        ema9  = calc_ema(close, 9)
        ema21 = calc_ema(close, 21)
        crossed_up  = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        trending_up = ema9.iloc[-1] > ema21.iloc[-1]
        ma_score = 30 if crossed_up else (15 if trending_up else 0)

        # Volume spike score
        avg_vol   = volume.iloc[-20:-1].mean()
        last_vol  = float(volume.iloc[-1])
        vol_ratio = (last_vol / avg_vol) if avg_vol > 0 else 1.0
        vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0

        return {
            "symbol":    symbol,
            "score":     round(rsi_score + ma_score + vol_score, 2),
            "rsi":       round(r, 2),
            "rsi_score": round(rsi_score, 2),
            "ma_score":  ma_score,
            "vol_score": round(vol_score, 2),
            "vol_ratio": round(vol_ratio, 2),
            "price":     float(close.iloc[-1]),
        }
    except Exception as e:
        log.info(f"⚠️ Score error {symbol}: {type(e).__name__}: {e}")
        return None

# ── Shared ticker fetch ────────────────────────────────────────

def fetch_tickers() -> pd.DataFrame:
    data = public_get("/api/v3/ticker/24hr")
    df   = pd.DataFrame(data)
    df   = df[df["symbol"].str.endswith("USDT")].copy()
    df["quoteVolume"]        = pd.to_numeric(df["quoteVolume"],        errors="coerce")
    df["priceChangePercent"] = pd.to_numeric(df["priceChangePercent"], errors="coerce")
    df["lastPrice"]          = pd.to_numeric(df["lastPrice"],          errors="coerce")
    df["abs_change"]         = df["priceChangePercent"].abs()
    return df.dropna(subset=["quoteVolume", "lastPrice"])

# ── Notional pre-check ─────────────────────────────────────────

def pick_tradeable(candidates: list, budget: float, label: str) -> dict | None:
    """Walk scored candidates in order, return first that passes lot/notional checks."""
    for c in candidates:
        step, min_qty, min_notional = get_symbol_rules(c["symbol"])
        qty      = round_qty(budget / c["price"], step)
        notional = round(qty * c["price"], 4)
        log.info(f"[{label}] Checking {c['symbol']} | price: {c['price']:.6f} | "
                 f"step: {step} | qty: {qty} | notional: ${notional:.2f} | min: ${min_notional:.2f}")
        if qty < min_qty:
            log.info(f"[{label}] Skip {c['symbol']} — qty {qty} < min {min_qty}")
            continue
        if notional < min_notional:
            log.info(f"[{label}] Skip {c['symbol']} — notional ${notional:.2f} < min ${min_notional:.2f}")
            continue
        return c
    log.info(f"[{label}] All candidates failed lot/notional checks.")
    return None

# ── Scanner: Scalper ───────────────────────────────────────────

def find_scalper_opportunity(tickers: pd.DataFrame, budget: float, exclude=None) -> dict | None:
    global last_top_scalper

    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[df["abs_change"]  >= 0.3]
    if exclude:
        df = df[df["symbol"] != exclude]

    candidates = df.sort_values("quoteVolume", ascending=False).head(80)["symbol"].tolist()[:40]
    log.info(f"🔍 [SCALPER] Scoring {len(candidates)} pairs...")

    scores = []
    for sym in candidates:
        result = score_pair(sym, interval="5m")
        if result:
            scores.append(result)
        time.sleep(0.1)
    scores.sort(key=lambda x: x["score"], reverse=True)

    if not scores:
        log.info("[SCALPER] No scoreable pairs.")
        return None

    best = scores[0]
    last_top_scalper = best
    ma_label = "crossover" if best["ma_score"] == 30 else ("trending" if best["ma_score"] == 15 else "flat")
    log.info(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
             f"RSI: {best['rsi']} ({best['rsi_score']:.0f}pts) | "
             f"MA: {ma_label} ({best['ma_score']}pts) | Vol: {best['vol_ratio']}x ({best['vol_score']:.0f}pts)")

    # Filter: must be above threshold AND not overbought
    tradeable = [s for s in scores
                 if s["score"] >= SCALPER_THRESHOLD and s["rsi"] <= SCALPER_MAX_RSI]
    if not tradeable:
        log.info(f"[SCALPER] No pair above threshold {SCALPER_THRESHOLD} with RSI <= {SCALPER_MAX_RSI}. Waiting...")
        return None

    return pick_tradeable(tradeable, budget, "SCALPER")

# ── Scanner: Moonshot ──────────────────────────────────────────

def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float, exclude=None) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"]        <= MOONSHOT_MAX_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    df = df[df["priceChangePercent"] >= 3.0]   # upward movers only
    if exclude:
        df = df[df["symbol"] != exclude]

    candidates = df.sort_values("priceChangePercent", ascending=False).head(30)["symbol"].tolist()
    log.info(f"🌙 [MOONSHOT] Scoring {len(candidates)} low-cap movers...")
    if not candidates:
        return None

    scores = []
    for sym in candidates:
        result = score_pair(sym, interval="15m")
        if result:
            scores.append(result)
        time.sleep(0.1)
    scores.sort(key=lambda x: x["score"], reverse=True)

    if not scores:
        log.info("[MOONSHOT] No scoreable pairs.")
        return None

    best = scores[0]
    last_top_alt = best
    log.info(f"🌙 [MOONSHOT] Top: {best['symbol']} | Score: {best['score']}/100 | "
             f"RSI: {best['rsi']} | Vol: {best['vol_ratio']}x | Price: {best['price']}")

    # Burst detection — confirm sudden activity in the last 15-30 minutes
    # We want to catch the START of a pump, not one that's already hours old
    tradeable = []
    for s in scores:
        if s["score"] < MOONSHOT_THRESHOLD:
            continue

        df15m = parse_klines(s["symbol"], interval="15m", limit=20)
        if df15m is None:
            tradeable.append(s)  # can't verify, give benefit of the doubt
            continue

        close  = df15m["close"].astype(float)
        volume = df15m["volume"].astype(float)

        # 1. Volume acceleration: last candle volume vs average of prior 10 candles
        avg_vol   = volume.iloc[-11:-1].mean()
        last_vol  = float(volume.iloc[-1])
        vol_burst = (last_vol / avg_vol) if avg_vol > 0 else 1.0

        # 2. Price acceleration: last candle % move vs average candle % move
        candle_moves  = (close - df15m["open"].astype(float)).abs() / df15m["open"].astype(float) * 100
        avg_move      = candle_moves.iloc[-11:-1].mean()
        last_move     = float(candle_moves.iloc[-1])
        price_burst   = (last_move / avg_move) if avg_move > 0 else 1.0

        # 3. Consecutive green candles: last 2 candles both green
        opens  = df15m["open"].astype(float)
        greens = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])

        log.info(f"[MOONSHOT] Burst check {s['symbol']} | "
                 f"Vol burst: {vol_burst:.1f}x | Price burst: {price_burst:.1f}x | "
                 f"Green candles: {greens}/2")

        # Require: volume at least 3x normal OR price move at least 2x normal
        # AND at least 1 of last 2 candles green (still moving up)
        if (vol_burst < 3.0 and price_burst < 2.0):
            log.info(f"[MOONSHOT] Skip {s['symbol']} — no burst detected")
            continue
        if greens == 0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — both recent candles red, burst may be over")
            continue

        tradeable.append(s)

    if not tradeable:
        log.info("[MOONSHOT] No pairs with burst activity detected.")
        return None

    return pick_tradeable(tradeable, budget, "MOONSHOT")

# ── Scanner: Reversal ──────────────────────────────────────────

def find_reversal_opportunity(tickers: pd.DataFrame, budget: float, exclude=None) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= REVERSAL_MIN_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    # Down at least 3% — looking for oversold bounces
    df = df[df["priceChangePercent"] <= -REVERSAL_MIN_DROP]
    if exclude:
        df = df[df["symbol"] != exclude]

    candidates = df.sort_values("priceChangePercent", ascending=True).head(30)["symbol"].tolist()
    log.info(f"🔄 [REVERSAL] Scoring {len(candidates)} oversold pairs...")
    if not candidates:
        return None

    tradeable = []
    for sym in candidates:
        # Fetch klines once, reuse for both scoring and green candle check
        df5m = parse_klines(sym, interval="5m", limit=60, min_len=30)
        if df5m is None:
            time.sleep(0.1)
            continue

        s = score_pair(sym, interval="5m")
        if s is None:
            time.sleep(0.1)
            continue

        # Must be deeply oversold
        if s["rsi"] > REVERSAL_MAX_RSI:
            time.sleep(0.1)
            continue

        # Last candle must be green — price has started recovering
        last_open  = float(df5m["open"].iloc[-1])
        last_close = float(df5m["close"].iloc[-1])
        if last_close <= last_open:
            log.info(f"[REVERSAL] Skip {sym} — last candle still red")
            time.sleep(0.1)
            continue

        tradeable.append(s)
        time.sleep(0.1)

    if not tradeable:
        log.info("[REVERSAL] No deeply oversold pairs with green candle.")
        return None

    tradeable.sort(key=lambda x: x["rsi"])  # lowest RSI first = most oversold
    best = tradeable[0]
    last_top_alt = best
    log.info(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | Price: {best['price']}")

    return pick_tradeable(tradeable, budget, "REVERSAL")

# ── Order execution ────────────────────────────────────────────

def place_order(symbol, side, qty, label=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] {side} {qty} {symbol} @ MARKET")
        return {"orderId": f"PAPER_{int(time.time())}", "paper": True}
    params = {"symbol": symbol, "side": side, "type": "MARKET", "quantity": qty}
    try:
        result = private_post("/api/v3/order", params)
        log.info(f"✅ [{label}] Order placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:
            error_body = e.response.json()
        except Exception:
            error_body = e.response.text if e.response is not None else "no response"
        log.error(f"🚨 [{label}] Order rejected: {error_body}")
        telegram(f"🚨 <b>Order rejected</b> [{label}]\n{symbol} {side} qty={qty}\nReason: {str(error_body)[:300]}")
        return None

# ── Trade lifecycle ────────────────────────────────────────────

def open_position(opp, budget_usdt, tp_pct, sl_pct, label, max_hours=None):
    symbol           = opp["symbol"]
    step, min_qty, _ = get_symbol_rules(symbol)

    # Always use a fresh price at order time
    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.warning(f"[{label}] Fresh price failed, using scored price: {e}")
        price = opp["price"]

    qty = round_qty(budget_usdt / price, step)
    if qty < min_qty:
        log.warning(f"[{label}] {symbol} qty {qty} below min {min_qty}, skipping.")
        return None

    notional = round(qty * price, 4)
    log.info(f"[{label}] Placing: {symbol} | qty: {qty} | price: ${price:.6f} | notional: ${notional:.2f}")

    order = place_order(symbol, "BUY", qty, label)
    if not order:
        return None

    trade = {
        "label":       label,
        "symbol":      symbol,
        "entry_price": price,
        "qty":         qty,
        "budget_used": round(budget_usdt, 2),
        "tp_price":    round(price * (1 + tp_pct), 8),
        "sl_price":    round(price * (1 - sl_pct), 8),
        "tp_pct":      tp_pct,
        "sl_pct":      sl_pct,
        "max_hours":   max_hours,
        "opened_at":   datetime.now(timezone.utc).isoformat(),
        "score":       opp["score"],
        "rsi":         opp.get("rsi", 0),
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons        = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄"}
    icon         = icons.get(label, "🟢")
    timeout_line = f"Max hold:    {max_hours}h\n" if max_hours else ""

    log.info(f"{icon} [{label}] Opened {symbol} | ${budget_usdt:.2f} | "
             f"Entry: {price:.6f} | TP: {trade['tp_price']:.6f} | SL: {trade['sl_price']:.6f}")
    telegram(
        f"{icon} <b>Trade Opened — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${budget_usdt:.2f} USDT</b>\n"
        f"Entry:       <b>${price:.6f}</b>\n"
        f"Take profit: <b>${trade['tp_price']:.6f}</b>  (+{tp_pct*100:.0f}%)\n"
        f"Stop loss:   <b>${trade['sl_price']:.6f}</b>  (-{sl_pct*100:.0f}%)\n"
        f"{timeout_line}"
        f"Score: {opp['score']} | RSI: {opp.get('rsi','?')} | Vol: {opp.get('vol_ratio','?')}x"
    )
    return trade


def check_exit(trade) -> tuple[bool, str]:
    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": trade["symbol"]})["price"])
    except Exception as e:
        log.error(f"Price fetch error for {trade['symbol']}: {e}")
        return False, ""

    label = trade["label"]
    pct   = (price - trade["entry_price"]) / trade["entry_price"] * 100

    if price >= trade["tp_price"]:
        log.info(f"🎯 [{label}] TP hit: {trade['symbol']} | +{pct:.2f}%")
        return True, "TAKE_PROFIT"
    if price <= trade["sl_price"]:
        log.info(f"🛑 [{label}] SL hit: {trade['symbol']} | {pct:.2f}%")
        return True, "STOP_LOSS"

    if trade.get("max_hours"):
        hours_held = (datetime.now(timezone.utc) -
                      datetime.fromisoformat(trade["opened_at"])).total_seconds() / 3600
        if hours_held >= trade["max_hours"]:
            log.info(f"⏰ [{label}] Timeout ({trade['max_hours']}h): {trade['symbol']} | {pct:+.2f}%")
            return True, "TIMEOUT"

    log.info(f"👀 [{label}] Holding {trade['symbol']} | {pct:+.2f}% | Price: {price:.6f}")
    return False, ""


def close_position(trade, reason):
    label  = trade["label"]
    symbol = trade["symbol"]
    place_order(symbol, "SELL", trade["qty"], label)

    try:
        exit_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except:
        exit_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]

    pnl_pct  = (exit_price - trade["entry_price"]) / trade["entry_price"] * 100
    pnl_usdt = (exit_price - trade["entry_price"]) * trade["qty"]
    trade_history.append({
        **trade,
        "exit_price":  exit_price,
        "exit_reason": reason,
        "closed_at":   datetime.now(timezone.utc).isoformat(),
        "pnl_pct":     round(pnl_pct, 4),
        "pnl_usdt":    round(pnl_usdt, 4),
    })

    wins      = [t for t in trade_history if t["pnl_pct"] > 0]
    win_rate  = len(wins) / len(trade_history) * 100
    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons     = {"TAKE_PROFIT": ("🎯","Take Profit Hit"), "STOP_LOSS": ("🛑","Stop Loss Hit"), "TIMEOUT": ("⏰","Timeout Exit")}
    emoji, reason_label = icons.get(reason, ("✅", reason))

    telegram(
        f"{emoji} <b>{reason_label} — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:    <b>{symbol}</b>\n"
        f"Entry:   ${trade['entry_price']:.6f}\n"
        f"Exit:    <b>${exit_price:.6f}</b>\n"
        f"P&L:     <b>{pnl_pct:+.2f}%  (${pnl_usdt:+.2f})</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Session: {len(trade_history)} trades | Win rate: {win_rate:.0f}% | Total P&L: ${total_pnl:+.2f}"
    )
    log.info(f"📈 Stats | Trades: {len(trade_history)} | Win rate: {win_rate:.0f}% | Total P&L: ${total_pnl:+.2f}")

# ── Heartbeat & daily summary ──────────────────────────────────

def send_heartbeat(balance: float):
    global last_heartbeat_at
    if time.time() - last_heartbeat_at < 3600:
        return
    last_heartbeat_at = time.time()

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    today        = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trades_today = len([t for t in trade_history if t.get("closed_at","")[:10] == today])

    def trade_line(trade, top_pair, label):
        if trade:
            try:
                price = float(public_get("/api/v3/ticker/price", {"symbol": trade["symbol"]})["price"])
                pct   = (price - trade["entry_price"]) / trade["entry_price"] * 100
                return f"{label}: <b>{trade['symbol']}</b> {pct:+.2f}%"
            except:
                return f"{label}: <b>{trade['symbol']}</b> (in trade)"
        if top_pair:
            return f"{label} watching: <b>{top_pair['symbol']}</b> (score {top_pair['score']})"
        return f"{label}: scanning..."

    alt_label = alt_trade["label"] if alt_trade else "ALT"
    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Bot is alive and running\n"
        f"Balance:      <b>${balance:.2f} USDT</b>\n"
        f"{trade_line(scalper_trade, last_top_scalper, 'Scalper')}\n"
        f"{trade_line(alt_trade, last_top_alt, alt_label)}\n"
        f"Trades today: {trades_today}"
    )


def send_daily_summary(balance: float):
    global last_daily_summary
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if last_daily_summary == today or datetime.now(timezone.utc).hour != 0:
        return
    last_daily_summary = today

    mode = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    if not trade_history:
        telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today. Still scanning.")
        return

    def block(label):
        trades = [t for t in trade_history if t.get("label") == label]
        if not trades:
            return ""
        wins = [t for t in trades if t["pnl_pct"] > 0]
        return (f"\n<b>{label}</b>: {len(trades)} trades | "
                f"Win rate: {len(wins)/len(trades)*100:.0f}% | "
                f"P&L: ${sum(t['pnl_usdt'] for t in trades):+.2f}")

    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    telegram(
        f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━"
        + block("SCALPER") + block("MOONSHOT") + block("REVERSAL")
        + f"\n━━━━━━━━━━━━━━━\nTotal P&L: <b>${total_pnl:+.2f}</b>\nBalance: <b>${balance:.2f} USDT</b>"
    )

# ── Main loop ──────────────────────────────────────────────────

def run():
    global scalper_trade, alt_trade

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")
    log.info(f"   Scalper : TP {SCALPER_TP*100}% / SL {SCALPER_SL*100}% / RSI max {SCALPER_MAX_RSI}")
    log.info(f"   Moonshot: TP {MOONSHOT_TP*100}% / SL {MOONSHOT_SL*100}% / max {MOONSHOT_MAX_HOURS}h")
    log.info(f"   Reversal: TP {REVERSAL_TP*100}% / SL {REVERSAL_SL*100}% / max {REVERSAL_MAX_HOURS}h")

    _load_exchange_info()

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (95% budget)\n"
        f"  TP: +{SCALPER_TP*100:.0f}%  |  SL: -{SCALPER_SL*100:.1f}%  |  RSI max {SCALPER_MAX_RSI}\n"
        f"\n🌙 <b>Moonshot</b> (5% budget — shares slot with Reversal)\n"
        f"  TP: +{MOONSHOT_TP*100:.0f}%  |  SL: -{MOONSHOT_SL*100:.0f}%  |  max {MOONSHOT_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b> (5% budget — shares slot with Moonshot)\n"
        f"  TP: +{REVERSAL_TP*100:.0f}%  |  SL: -{REVERSAL_SL*100:.0f}%  |  max {REVERSAL_MAX_HOURS}h"
    )

    scalper_excluded = None
    alt_excluded     = None

    while True:
        try:
            balance = get_available_balance()

            # Only fetch tickers when we actually need to scan
            need_scalper_scan = scalper_trade is None
            need_alt_scan     = alt_trade is None
            tickers = fetch_tickers() if (need_scalper_scan or need_alt_scan) else None

            # ── Scalper leg ───────────────────────────────────────
            if scalper_trade is None:
                budget = round(balance * SCALPER_BUDGET_PCT, 2)
                opp    = find_scalper_opportunity(tickers, budget, exclude=scalper_excluded)
                if opp:
                    scalper_trade    = open_position(opp, budget, SCALPER_TP, SCALPER_SL, "SCALPER")
                    scalper_excluded = None
            else:
                should_exit, reason = check_exit(scalper_trade)
                if should_exit:
                    scalper_excluded = scalper_trade["symbol"]
                    close_position(scalper_trade, reason)
                    scalper_trade = None
                    log.info("🔄 [SCALPER] Closed. Re-scanning next cycle...")

            # ── Alt leg (Moonshot OR Reversal — whichever fires first) ─
            if alt_trade is None:
                budget = round(balance * MOONSHOT_BUDGET_PCT, 2)

                # Try moonshot first, fall back to reversal
                opp = find_moonshot_opportunity(tickers, budget, exclude=alt_excluded)
                if opp:
                    alt_trade    = open_position(opp, budget, MOONSHOT_TP, MOONSHOT_SL,
                                                 "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                    alt_excluded = None
                else:
                    opp = find_reversal_opportunity(tickers, budget, exclude=alt_excluded)
                    if opp:
                        alt_trade    = open_position(opp, budget, REVERSAL_TP, REVERSAL_SL,
                                                     "REVERSAL", max_hours=REVERSAL_MAX_HOURS)
                        alt_excluded = None
            else:
                should_exit, reason = check_exit(alt_trade)
                if should_exit:
                    closed_label = alt_trade["label"]
                    alt_excluded = alt_trade["symbol"]
                    close_position(alt_trade, reason)
                    alt_trade = None
                    log.info(f"🔄 [{closed_label}] Closed. Re-scanning next cycle...")

            send_heartbeat(balance)
            send_daily_summary(balance)
            # Sleep shorter while monitoring active trades, longer when just scanning
            time.sleep(15 if (scalper_trade or alt_trade) else SCAN_INTERVAL)

        except KeyboardInterrupt:
            log.info("🛑 Stopped.")
            for t in [scalper_trade, alt_trade]:
                if t:
                    log.warning(f"⚠️  Still holding {t['symbol']} ({t['label']}) — close manually if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway — it may need restarting.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nWill retry in 30s.")
            time.sleep(30)

run()
