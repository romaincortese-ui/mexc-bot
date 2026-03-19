"""
MEXC Scalping Bot + Moonshot Strategy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Two parallel strategies:
  1. Scalper  — 95% of balance | TP: +2%  | SL: -1.5% | high-volume pairs
  2. Moonshot —  5% of balance | TP: +25% | SL: -10%  | low-volume gems
     + Moonshot auto-exits after 48h if TP not reached

SETUP: Fill in your MEXC API details below, then hit Run.
       Leave PAPER_TRADE = True until you've watched it work.
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

# ── Scalper settings ───────────────────────────────────────────
SCALPER_BUDGET_PCT  = 0.95    # 95% of available balance
SCALPER_TP          = 0.020   # +2.0%
SCALPER_SL          = 0.015   # -1.5%
SCALPER_MIN_VOL     = 500_000 # min 24h USDT volume
SCALPER_THRESHOLD   = 20      # min signal score to enter

# ── Moonshot settings ──────────────────────────────────────────
MOONSHOT_BUDGET_PCT = 0.05    # 5% of available balance
MOONSHOT_TP         = 0.25    # +25%
MOONSHOT_SL         = 0.10    # -10%
MOONSHOT_MAX_VOL    = 200_000 # max 24h volume (keeps it low-cap)
MOONSHOT_MIN_VOL    = 10_000  # min volume (avoid ghost coins)
MOONSHOT_THRESHOLD  = 25      # slightly higher bar
MOONSHOT_MAX_HOURS  = 48      # exit after 48h regardless

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
moonshot_trade     = None
last_heartbeat_at  = 0
last_daily_summary = ""
last_top_scalper   = None
last_top_moonshot  = None

# Cache exchange info so we don't fetch 1000+ symbols on every order
_exchange_info_cache    = {}
_exchange_info_fetched  = False

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

def _sign(params):
    query = "&".join(f"{k}={v}" for k, v in sorted(params.items()))
    return hmac.new(MEXC_API_SECRET.encode(), query.encode(), hashlib.sha256).hexdigest()

def public_get(path, params=None):
    r = requests.get(BASE_URL + path, params=params or {}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_get(path, params=None):
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    params["signature"] = _sign(params)
    r = requests.get(BASE_URL + path, params=params,
                     headers={"X-MEXC-APIKEY": MEXC_API_KEY}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_post(path, params=None):
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    params["signature"] = _sign(params)
    r = requests.post(BASE_URL + path, params=params,
                      headers={"X-MEXC-APIKEY": MEXC_API_KEY}, timeout=10)
    r.raise_for_status()
    return r.json()

# ── Exchange info cache ────────────────────────────────────────

def _load_exchange_info():
    """Fetch and cache lot size + min notional rules for all symbols. Called once at startup."""
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
            _exchange_info_cache[sym] = {
                "step":         step,
                "min_qty":      min_qty,
                "min_notional": min_notional,
            }
        _exchange_info_fetched = True
        log.info(f"📋 Loaded rules for {len(_exchange_info_cache)} symbols.")
    except Exception as e:
        log.error(f"Failed to load exchange info: {e}")

def get_symbol_rules(symbol):
    """Return (step, min_qty, min_notional) from cache. Falls back to safe defaults."""
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
    """
    Floor qty to the nearest valid step using integer arithmetic
    to avoid floating point artifacts (e.g. 5731.9999999).
    """
    if step <= 0:
        return qty
    # Scale both to integers, do integer division, scale back
    scale    = int(round(1 / step)) if step < 1 else 1
    floored  = int(qty * scale) // int(step * scale)
    result   = floored * step
    # Determine decimal places from step
    decimals = max(0, -int(np.floor(np.log10(step)))) if step < 1 else 0
    return round(result, decimals)

# ── Indicators ─────────────────────────────────────────────────

def rsi(series, period=14):
    delta = series.diff()
    gain  = delta.clip(lower=0).rolling(period).mean()
    loss  = (-delta.clip(upper=0)).rolling(period).mean()
    rs    = gain / loss.replace(0, np.nan)
    return 100 - (100 / (1 + rs))

# ── Pair scoring ───────────────────────────────────────────────

def score_pair(symbol, interval="5m"):
    try:
        data = public_get("/api/v3/klines", {"symbol": symbol, "interval": interval, "limit": 60})
        if not data:
            return None
        # MEXC returns variable column counts — read by position
        df = pd.DataFrame(data)
        df.columns = range(len(df.columns))
        df = df.rename(columns={0: "open_time", 1: "open", 2: "high",
                                 3: "low",       4: "close", 5: "volume"})
        df["close"]  = pd.to_numeric(df["close"],  errors="coerce")
        df["volume"] = pd.to_numeric(df["volume"], errors="coerce")
        df = df.dropna(subset=["close", "volume"])
        if len(df) < 30:
            return None

        close  = df["close"]
        volume = df["volume"]

        r = rsi(close).iloc[-1]
        if np.isnan(r):
            return None
        rsi_score = max(0, 40 - r) if r < 50 else 0

        ema9  = close.ewm(span=9,  adjust=False).mean()
        ema21 = close.ewm(span=21, adjust=False).mean()
        crossed_up  = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        trending_up = ema9.iloc[-1] > ema21.iloc[-1]
        ma_score = 30 if crossed_up else (15 if trending_up else 0)

        avg_vol   = volume.iloc[-20:-1].mean()
        vol_ratio = last_vol / avg_vol if (avg_vol > 0 and (last_vol := volume.iloc[-1]) > 0) else 1
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
        log.info(f"⚠️ Error scoring {symbol}: {type(e).__name__}: {e}")
        return None

# ── Shared ticker fetch ────────────────────────────────────────

def fetch_tickers() -> pd.DataFrame:
    """Fetch 24h ticker for all USDT pairs. Called once per scan cycle, shared by both strategies."""
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
    """
    Walk a list of scored pairs in score order.
    Return the first one that passes lot size and notional checks.
    """
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

# ── Scanners ───────────────────────────────────────────────────

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

    if not scores:
        log.info("[SCALPER] No scoreable pairs found.")
        return None

    scores.sort(key=lambda x: x["score"], reverse=True)
    best = scores[0]
    last_top_scalper = best

    ma_label = "crossover" if best["ma_score"] == 30 else ("trending" if best["ma_score"] == 15 else "flat")
    log.info(
        f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
        f"RSI: {best['rsi']} ({best['rsi_score']:.0f}pts) | "
        f"MA: {ma_label} ({best['ma_score']}pts) | "
        f"Vol: {best['vol_ratio']}x ({best['vol_score']:.0f}pts)"
    )

    above_threshold = [s for s in scores if s["score"] >= SCALPER_THRESHOLD]
    if not above_threshold:
        log.info(f"[SCALPER] Best score {best['score']} below threshold {SCALPER_THRESHOLD}. Waiting...")
        return None

    return pick_tradeable(above_threshold, budget, "SCALPER")


def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float, exclude=None) -> dict | None:
    global last_top_moonshot

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"]        <= MOONSHOT_MAX_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    df = df[df["priceChangePercent"] >= 3.0]   # upward movers only, at least +3%
    if exclude:
        df = df[df["symbol"] != exclude]

    candidates = df.sort_values("priceChangePercent", ascending=False).head(30)["symbol"].tolist()
    log.info(f"🌙 [MOONSHOT] Scoring {len(candidates)} low-cap movers...")

    if not candidates:
        log.info("[MOONSHOT] No low-cap movers found.")
        return None

    scores = []
    for sym in candidates:
        result = score_pair(sym, interval="15m")
        if result:
            scores.append(result)
        time.sleep(0.1)

    if not scores:
        log.info("[MOONSHOT] No scoreable pairs found.")
        return None

    scores.sort(key=lambda x: x["score"], reverse=True)
    best = scores[0]
    last_top_moonshot = best

    log.info(
        f"🌙 [MOONSHOT] Top: {best['symbol']} | Score: {best['score']}/100 | "
        f"RSI: {best['rsi']} | Vol: {best['vol_ratio']}x | Price: {best['price']}"
    )

    above_threshold = [s for s in scores if s["score"] >= MOONSHOT_THRESHOLD]
    if not above_threshold:
        log.info(f"[MOONSHOT] Best score {best['score']} below threshold {MOONSHOT_THRESHOLD}. Waiting...")
        return None

    return pick_tradeable(above_threshold, budget, "MOONSHOT")

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

def open_position(opp, budget_usdt, tp_pct, sl_pct, label):
    symbol           = opp["symbol"]
    step, min_qty, _ = get_symbol_rules(symbol)

    # Fetch fresh price right before ordering — score_pair price may be stale
    try:
        ticker = public_get("/api/v3/ticker/price", {"symbol": symbol})
        price  = float(ticker["price"])
    except Exception as e:
        log.warning(f"[{label}] Could not fetch fresh price for {symbol}, using scored price: {e}")
        price = opp["price"]

    qty = round_qty(budget_usdt / price, step)

    if qty < min_qty:
        log.warning(f"[{label}] {symbol} qty {qty} below min {min_qty} at fresh price, skipping.")
        return None

    notional = round(qty * price, 4)
    log.info(f"[{label}] Placing order: {symbol} | qty: {qty} | price: ${price:.6f} | notional: ${notional:.2f}")

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
        "opened_at":   datetime.now(timezone.utc).isoformat(),
        "score":       opp["score"],
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icon         = "🌙" if label == "MOONSHOT" else "🟢"
    timeout_line = "Max hold:    48 hours\n" if label == "MOONSHOT" else ""

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
        f"Score: {opp['score']} | RSI: {opp['rsi']} | Vol: {opp['vol_ratio']}x"
    )
    return trade


def check_exit(trade) -> tuple[bool, str]:
    try:
        ticker = public_get("/api/v3/ticker/price", {"symbol": trade["symbol"]})
        price  = float(ticker["price"])
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
    if label == "MOONSHOT":
        hours_held = (datetime.now(timezone.utc) -
                      datetime.fromisoformat(trade["opened_at"])).total_seconds() / 3600
        if hours_held >= MOONSHOT_MAX_HOURS:
            log.info(f"⏰ [MOONSHOT] 48h timeout: {trade['symbol']} | {pct:+.2f}%")
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

    icons = {"TAKE_PROFIT": ("🎯","Take Profit Hit"), "STOP_LOSS": ("🛑","Stop Loss Hit"), "TIMEOUT": ("⏰","48h Timeout")}
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

# ── Heartbeat ──────────────────────────────────────────────────

def send_heartbeat(balance: float):
    global last_heartbeat_at
    if time.time() - last_heartbeat_at < 3600:
        return
    last_heartbeat_at = time.time()

    mode        = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    today       = datetime.now(timezone.utc).strftime("%Y-%m-%d")
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

    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Bot is alive and running\n"
        f"Balance:      <b>${balance:.2f} USDT</b>\n"
        f"{trade_line(scalper_trade,  last_top_scalper,  'Scalper')}\n"
        f"{trade_line(moonshot_trade, last_top_moonshot, 'Moonshot')}\n"
        f"Trades today: {trades_today}"
    )

# ── Daily summary ──────────────────────────────────────────────

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
            return f"\n<b>{label}</b>: no trades"
        wins = [t for t in trades if t["pnl_pct"] > 0]
        return (f"\n<b>{label}</b>: {len(trades)} trades | "
                f"Win rate: {len(wins)/len(trades)*100:.0f}% | "
                f"P&L: ${sum(t['pnl_usdt'] for t in trades):+.2f}")

    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    telegram(
        f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━"
        + block("SCALPER") + block("MOONSHOT")
        + f"\n━━━━━━━━━━━━━━━\nTotal P&L: <b>${total_pnl:+.2f}</b>\nBalance: <b>${balance:.2f} USDT</b>"
    )

# ── Main loop ──────────────────────────────────────────────────

def run():
    global scalper_trade, moonshot_trade

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")
    log.info(f"   Scalper : TP {SCALPER_TP*100}% / SL {SCALPER_SL*100}%")
    log.info(f"   Moonshot: TP {MOONSHOT_TP*100}% / SL {MOONSHOT_SL*100}% / max 48h")

    _load_exchange_info()  # cache lot sizes once at startup

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n<b>Scalper</b> (95% budget)\n"
        f"  TP: +{SCALPER_TP*100:.0f}%  |  SL: -{SCALPER_SL*100:.1f}%\n"
        f"  High-volume pairs\n"
        f"\n<b>Moonshot</b> (5% budget)\n"
        f"  TP: +{MOONSHOT_TP*100:.0f}%  |  SL: -{MOONSHOT_SL*100:.0f}%\n"
        f"  Low-cap gems | 48h max hold"
    )

    scalper_excluded  = None
    moonshot_excluded = None

    while True:
        try:
            balance = get_available_balance()

            # Fetch tickers once, share between both strategies
            tickers = fetch_tickers()

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

            # ── Moonshot leg ──────────────────────────────────────
            if moonshot_trade is None:
                budget = round(balance * MOONSHOT_BUDGET_PCT, 2)
                opp    = find_moonshot_opportunity(tickers, budget, exclude=moonshot_excluded)
                if opp:
                    moonshot_trade    = open_position(opp, budget, MOONSHOT_TP, MOONSHOT_SL, "MOONSHOT")
                    moonshot_excluded = None
            else:
                should_exit, reason = check_exit(moonshot_trade)
                if should_exit:
                    moonshot_excluded = moonshot_trade["symbol"]
                    close_position(moonshot_trade, reason)
                    moonshot_trade = None
                    log.info("🔄 [MOONSHOT] Closed. Re-scanning next cycle...")

            send_heartbeat(balance)
            send_daily_summary(balance)
            time.sleep(15)

        except KeyboardInterrupt:
            log.info("🛑 Stopped.")
            for t in [scalper_trade, moonshot_trade]:
                if t:
                    log.warning(f"⚠️  Still holding {t['symbol']} ({t['label']}) — close manually if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway — it may need restarting.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nWill retry in 30s.")
            time.sleep(30)

run()
