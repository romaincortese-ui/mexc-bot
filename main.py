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
from collections import defaultdict, Counter
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG — edit these values before running
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = "mx0vglg1LIlEl98JhQ"
MEXC_API_SECRET = "2b53b21288c8494bbec5e0cc7f34d8c2"

PAPER_TRADE   = False    # ← keep True until ready for real money
PAPER_BALANCE = 50.0    # simulated starting balance

# ── Scalper (main strategy — momentum) ────────────────────────
SCALPER_BUDGET_PCT  = 0.95      # 95% of available balance
SCALPER_TP          = 0.020     # +2.0%
SCALPER_SL          = 0.015     # -1.5%
SCALPER_MIN_VOL     = 1_000_000 # min 24h USDT volume
SCALPER_MIN_PRICE   = 0.01      # min price — avoids slippage on ultra-cheap coins
SCALPER_THRESHOLD   = 20        # min signal score to enter
SCALPER_MAX_RSI     = 70        # don't enter overbought pairs

# ── Moonshot (breakout — low-cap gems) ────────────────────────
MOONSHOT_BUDGET_PCT = 0.05      # 5% of available balance
MOONSHOT_TP         = 0.25      # +25%
MOONSHOT_SL         = 0.10      # -10%
MOONSHOT_MAX_VOL    = 200_000   # max 24h volume (keeps it low-cap)
MOONSHOT_MIN_VOL    = 10_000    # min volume (avoid ghost coins)
MOONSHOT_THRESHOLD  = 25        # min signal score
MOONSHOT_MAX_HOURS  = 48        # exit after 48h regardless

# ── Reversal (mean reversion — oversold bounce) ────────────────
REVERSAL_BUDGET_PCT = 0.05      # shares 5% slot with moonshot
REVERSAL_TP         = 0.030     # +3%
REVERSAL_SL         = 0.020     # -2%
REVERSAL_MIN_VOL    = 100_000   # needs some liquidity
REVERSAL_MAX_RSI    = 32        # only enter deeply oversold pairs
REVERSAL_MIN_DROP   = 3.0       # pair must be down at least 3% in 24h
REVERSAL_MAX_HOURS  = 4         # exit after 4h regardless

# ── Shared ────────────────────────────────────────────────────
MIN_PRICE     = 0.001   # global floor (moonshot/reversal)
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
trade_history        = []
scalper_trade        = None
alt_trade            = None
last_heartbeat_at    = 0
last_daily_summary   = ""
last_weekly_summary  = ""
last_telegram_update = 0
last_top_scalper     = None
last_top_alt         = None

_symbol_rules         = {}
_symbol_rules_fetched = False
_symbol_rules_at      = 0

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

def private_delete(path, params=None):
    """DELETE request — required for order cancellation on MEXC."""
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    query  = "&".join(f"{k}={v}" for k, v in params.items())
    params["signature"] = hmac.new(
        MEXC_API_SECRET.encode(), query.encode(), hashlib.sha256
    ).hexdigest()
    r = requests.delete(BASE_URL + path, params=params,
                        headers={"X-MEXC-APIKEY": MEXC_API_KEY}, timeout=10)
    r.raise_for_status()
    return r.json()

# ── Symbol rules cache ────────────────────────────────────────

def _load_symbol_rules():
    global _symbol_rules_fetched, _symbol_rules_at
    if _symbol_rules_fetched and (time.time() - _symbol_rules_at) < 86400:
        return
    log.info("📋 Loading symbol rules...")
    try:
        info = public_get("/api/v3/exchangeInfo")
        for s in info.get("symbols", []):
            sym          = s["symbol"]
            min_qty      = 1.0
            min_notional = 1.0
            for f in s.get("filters", []):
                if f["filterType"] == "LOT_SIZE":
                    min_qty = float(f.get("minQty", 1.0))
                if f["filterType"] == "MIN_NOTIONAL":
                    min_notional = float(f.get("minNotional", 1.0))
            _symbol_rules[sym] = {"min_qty": min_qty, "min_notional": min_notional}
        _symbol_rules_fetched = True
        _symbol_rules_at      = time.time()
        log.info(f"📋 Loaded rules for {len(_symbol_rules)} symbols.")
    except Exception as e:
        log.error(f"Failed to load symbol rules: {e}")

def get_symbol_rules(symbol):
    rules = _symbol_rules.get(symbol)
    if rules:
        return rules["min_qty"], rules["min_notional"]
    return 1.0, 1.0

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

# ── Kline parsing ──────────────────────────────────────────────

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
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

# ── Pair scoring ───────────────────────────────────────────────

def score_pair(symbol: str, interval: str = "5m", df: pd.DataFrame = None) -> dict | None:
    """Score a pair. Accepts pre-fetched df to avoid duplicate API calls."""
    if df is None:
        df = parse_klines(symbol, interval)
    if df is None:
        return None
    try:
        close  = df["close"]
        volume = df["volume"]

        r = calc_rsi(close)
        if np.isnan(r):
            return None

        rsi_score = max(0, 40 - r) if r < 50 else 0

        ema9  = calc_ema(close, 9)
        ema21 = calc_ema(close, 21)
        crossed_up  = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        trending_up = ema9.iloc[-1] > ema21.iloc[-1]
        ma_score = 30 if crossed_up else (15 if trending_up else 0)

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
    df["volume"]             = pd.to_numeric(df["volume"],             errors="coerce")
    df["priceChangePercent"] = pd.to_numeric(df["priceChangePercent"], errors="coerce")
    df["lastPrice"]          = pd.to_numeric(df["lastPrice"],          errors="coerce")
    df["abs_change"]         = df["priceChangePercent"].abs()
    return df.dropna(subset=["quoteVolume", "lastPrice"])

# ── Notional pre-check ─────────────────────────────────────────

def pick_tradeable(candidates: list, budget: float, label: str) -> dict | None:
    for c in candidates:
        min_qty, min_notional = get_symbol_rules(c["symbol"])
        qty      = int(budget / c["price"])
        notional = round(qty * c["price"], 4)
        log.info(f"[{label}] Checking {c['symbol']} | price: {c['price']:.6f} | "
                 f"qty: {qty} | notional: ${notional:.2f} | min: ${min_notional:.2f}")
        if qty < min_qty:
            log.info(f"[{label}] Skip {c['symbol']} — qty {qty} < min {min_qty}")
            continue
        if notional < min_notional:
            log.info(f"[{label}] Skip {c['symbol']} — notional ${notional:.2f} < min ${min_notional:.2f}")
            continue
        return c
    log.info(f"[{label}] All candidates failed notional/qty checks.")
    return None

# ── Scanner: Scalper ───────────────────────────────────────────

def find_scalper_opportunity(tickers: pd.DataFrame, budget: float,
                              exclude=None, open_symbols: set = None) -> dict | None:
    global last_top_scalper

    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= SCALPER_MIN_PRICE]
    df = df[df["abs_change"]  >= 0.3]
    if exclude:      df = df[df["symbol"] != exclude]
    if open_symbols: df = df[~df["symbol"].isin(open_symbols)]

    candidates = df.sort_values("quoteVolume", ascending=False).head(80)["symbol"].tolist()[:40]
    log.info(f"🔍 [SCALPER] Scoring {len(candidates)} pairs (min vol: ${SCALPER_MIN_VOL:,})...")

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

    best     = scores[0]
    last_top_scalper = best
    vol_row  = tickers[tickers["symbol"] == best["symbol"]]
    best_vol = float(vol_row["quoteVolume"].iloc[0]) if not vol_row.empty else 0
    ma_label = "crossover" if best["ma_score"] == 30 else ("trending" if best["ma_score"] == 15 else "flat")
    log.info(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
             f"24h vol: ${best_vol:,.0f} | RSI: {best['rsi']} ({best['rsi_score']:.0f}pts) | "
             f"MA: {ma_label} ({best['ma_score']}pts) | Vol: {best['vol_ratio']}x ({best['vol_score']:.0f}pts)")

    tradeable = [s for s in scores
                 if s["score"] >= SCALPER_THRESHOLD and s["rsi"] <= SCALPER_MAX_RSI]
    if not tradeable:
        log.info(f"[SCALPER] Best score {best['score']} or RSI {best['rsi']} outside thresholds. Waiting...")
        return None

    return pick_tradeable(tradeable, budget, "SCALPER")

# ── Scanner: Moonshot ──────────────────────────────────────────

def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float,
                               exclude=None, open_symbols: set = None) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"]        <= MOONSHOT_MAX_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    df = df[df["priceChangePercent"] >= 3.0]
    if exclude:      df = df[df["symbol"] != exclude]
    if open_symbols: df = df[~df["symbol"].isin(open_symbols)]

    candidates = df.sort_values("priceChangePercent", ascending=False).head(30)["symbol"].tolist()
    log.info(f"🌙 [MOONSHOT] Scoring {len(candidates)} low-cap movers...")
    if not candidates:
        return None

    scores = []
    for sym in candidates:
        df15m = parse_klines(sym, interval="15m", limit=60)
        if df15m is None:
            time.sleep(0.1)
            continue
        result = score_pair(sym, interval="15m", df=df15m)
        if result:
            result["_df"] = df15m
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

    tradeable = []
    for s in scores:
        if s["score"] < MOONSHOT_THRESHOLD:
            continue
        df15m = s.pop("_df", None)
        if df15m is None or len(df15m) < 12:
            tradeable.append(s)
            continue

        close  = df15m["close"]
        volume = df15m["volume"]
        opens  = df15m["open"]

        avg_vol     = volume.iloc[-11:-1].mean()
        vol_burst   = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        candle_moves= (close - opens).abs() / opens * 100
        avg_move    = candle_moves.iloc[-11:-1].mean()
        price_burst = (float(candle_moves.iloc[-1]) / avg_move) if avg_move > 0 else 1.0
        greens      = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])

        log.info(f"[MOONSHOT] Burst {s['symbol']} | Vol: {vol_burst:.1f}x | "
                 f"Price: {price_burst:.1f}x | Green: {greens}/2")

        if vol_burst < 3.0 and price_burst < 2.0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — no burst")
            continue
        if greens == 0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — both candles red")
            continue
        tradeable.append(s)

    if not tradeable:
        log.info("[MOONSHOT] No pairs with burst activity.")
        return None

    return pick_tradeable(tradeable, budget, "MOONSHOT")

# ── Scanner: Reversal ──────────────────────────────────────────

def find_reversal_opportunity(tickers: pd.DataFrame, budget: float,
                               exclude=None, open_symbols: set = None) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= REVERSAL_MIN_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    df = df[df["priceChangePercent"] <= -REVERSAL_MIN_DROP]
    if exclude:      df = df[df["symbol"] != exclude]
    if open_symbols: df = df[~df["symbol"].isin(open_symbols)]

    candidates = df.sort_values("priceChangePercent", ascending=True).head(30)["symbol"].tolist()
    log.info(f"🔄 [REVERSAL] Scoring {len(candidates)} oversold pairs...")
    if not candidates:
        return None

    tradeable = []
    for sym in candidates:
        df5m = parse_klines(sym, interval="5m", limit=60, min_len=30)
        if df5m is None:
            time.sleep(0.1)
            continue
        s = score_pair(sym, interval="5m", df=df5m)
        if s is None or s["rsi"] > REVERSAL_MAX_RSI:
            time.sleep(0.1)
            continue
        if float(df5m["close"].iloc[-1]) <= float(df5m["open"].iloc[-1]):
            log.info(f"[REVERSAL] Skip {sym} — last candle red")
            time.sleep(0.1)
            continue
        tradeable.append(s)
        time.sleep(0.1)

    if not tradeable:
        log.info("[REVERSAL] No deeply oversold pairs with green candle.")
        return None

    tradeable.sort(key=lambda x: x["rsi"])
    best = tradeable[0]
    last_top_alt = best
    log.info(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | Price: {best['price']}")

    return pick_tradeable(tradeable, budget, "REVERSAL")

# ── Order execution ────────────────────────────────────────────

def place_market_buy(symbol, qty, label=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] BUY {qty} {symbol} @ MARKET")
        return {"orderId": f"PAPER_BUY_{int(time.time())}"}
    params = {"symbol": symbol, "side": "BUY", "type": "MARKET", "quantity": qty}
    try:
        result = private_post("/api/v3/order", params)
        log.info(f"✅ [{label}] BUY placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:    error_body = e.response.json()
        except: error_body = e.response.text if e.response else "no response"
        log.error(f"🚨 [{label}] BUY rejected: {error_body}")
        telegram(f"🚨 <b>BUY rejected</b> [{label}]\n{symbol} qty={qty}\nReason: {str(error_body)[:300]}")
        return None


def place_limit_sell(symbol, qty, price, label="", tag=""):
    """Place a limit sell. Price passed as-is — caller is responsible for rounding."""
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] LIMIT SELL {qty} {symbol} @ {price} ({tag})")
        return f"PAPER_{tag}_{int(time.time())}"
    params = {"symbol": symbol, "side": "SELL", "type": "LIMIT",
              "quantity": qty, "price": str(price)}
    try:
        result   = private_post("/api/v3/order", params)
        order_id = result.get("orderId")
        log.info(f"✅ [{label}] LIMIT SELL ({tag}) placed: {order_id} @ {price}")
        return order_id
    except requests.exceptions.HTTPError as e:
        try:    error_body = e.response.json()
        except: error_body = e.response.text if e.response else "no response"
        log.error(f"🚨 [{label}] LIMIT SELL rejected ({tag}): {error_body}")
        return None


def cancel_order(symbol, order_id, label=""):
    """Cancel a limit order using DELETE — the correct MEXC method."""
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] Cancel {order_id}")
        return
    try:
        private_delete("/api/v3/order", {"symbol": symbol, "orderId": order_id})
        log.info(f"✅ [{label}] Cancelled {order_id}")
    except Exception as e:
        log.debug(f"[{label}] Cancel {order_id} failed (may already be filled): {e}")


def get_open_order_ids(symbol) -> set:
    """
    Return set of open order IDs for a symbol in a single API call.
    Used to check if TP/SL orders are still open or have been filled/cancelled.
    """
    if PAPER_TRADE:
        return set()
    try:
        orders = private_get("/api/v3/openOrders", {"symbol": symbol})
        return {o["orderId"] for o in orders}
    except Exception as e:
        log.debug(f"get_open_order_ids error {symbol}: {e}")
        return set()

# ── Trade lifecycle ────────────────────────────────────────────

def open_position(opp, budget_usdt, tp_pct, sl_pct, label, max_hours=None):
    symbol                = opp["symbol"]
    min_qty, min_notional = get_symbol_rules(symbol)

    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.warning(f"[{label}] Fresh price failed, using scored price: {e}")
        price = opp["price"]

    qty      = int(budget_usdt / price)
    notional = round(qty * price, 4)

    if qty < min_qty:
        log.warning(f"[{label}] {symbol} qty {qty} < min {min_qty}, skipping.")
        return None
    if notional < min_notional:
        log.warning(f"[{label}] {symbol} notional ${notional:.2f} < min ${min_notional:.2f}, skipping.")
        return None

    log.info(f"[{label}] Placing BUY: {symbol} | qty: {qty} | price: ${price:.6f} | notional: ${notional:.2f}")

    buy_order = place_market_buy(symbol, qty, label)
    if not buy_order:
        return None

    tp_price = round(price * (1 + tp_pct), 8)
    sl_price = round(price * (1 - sl_pct), 8)

    tp_order_id = place_limit_sell(symbol, qty, tp_price, label, tag="TP")
    sl_order_id = place_limit_sell(symbol, qty, sl_price, label, tag="SL")

    if not PAPER_TRADE and not tp_order_id and not sl_order_id:
        log.warning(f"[{label}] Both limit orders failed — bot will use price polling as fallback.")
        telegram(f"⚠️ [{label}] Limit orders failed for {symbol} — monitoring manually.")

    trade = {
        "label":        label,
        "symbol":       symbol,
        "entry_price":  price,
        "qty":          qty,
        "budget_used":  round(budget_usdt, 2),
        "tp_price":     tp_price,
        "sl_price":     sl_price,
        "tp_pct":       tp_pct,
        "sl_pct":       sl_pct,
        "tp_order_id":  tp_order_id,
        "sl_order_id":  sl_order_id,
        "max_hours":    max_hours,
        "opened_at":    datetime.now(timezone.utc).isoformat(),
        "score":        opp["score"],
        "rsi":          opp.get("rsi", 0),
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons        = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄"}
    icon         = icons.get(label, "🟢")
    timeout_line = f"Max hold:    {max_hours}h\n" if max_hours else ""
    orders_line  = ("Exchange orders: TP ✅  SL ✅" if (tp_order_id and sl_order_id)
                    else "Exchange orders: price polling (limit orders failed)")

    log.info(f"{icon} [{label}] Opened {symbol} | ${budget_usdt:.2f} | "
             f"Entry: {price:.6f} | TP: {tp_price:.6f} | SL: {sl_price:.6f}")
    telegram(
        f"{icon} <b>Trade Opened — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${budget_usdt:.2f} USDT</b>\n"
        f"Entry:       <b>${price:.6f}</b>\n"
        f"Take profit: <b>${tp_price:.6f}</b>  (+{tp_pct*100:.0f}%)\n"
        f"Stop loss:   <b>${sl_price:.6f}</b>  (-{sl_pct*100:.0f}%)\n"
        f"{timeout_line}"
        f"{orders_line}\n"
        f"Score: {opp['score']} | RSI: {opp.get('rsi','?')} | Vol: {opp.get('vol_ratio','?')}x"
    )
    return trade


def check_exit(trade) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")
    sl_order_id = trade.get("sl_order_id")

    # ── Timeout (always bot-side — exchange can't do time exits) ──
    if trade.get("max_hours"):
        hours_held = (datetime.now(timezone.utc) -
                      datetime.fromisoformat(trade["opened_at"])).total_seconds() / 3600
        if hours_held >= trade["max_hours"]:
            log.info(f"⏰ [{label}] Timeout ({trade['max_hours']}h): {symbol}")
            if not PAPER_TRADE:
                if tp_order_id: cancel_order(symbol, tp_order_id, label)
                if sl_order_id: cancel_order(symbol, sl_order_id, label)
            return True, "TIMEOUT"

    # ── Paper mode or both limit orders failed — use price polling ──
    use_polling = PAPER_TRADE or (not tp_order_id and not sl_order_id)
    if use_polling:
        try:
            price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
        except Exception as e:
            log.error(f"Price fetch error for {symbol}: {e}")
            return False, ""
        pct = (price - trade["entry_price"]) / trade["entry_price"] * 100
        if price >= trade["tp_price"]:
            log.info(f"🎯 [{label}] TP hit: {symbol} | +{pct:.2f}%")
            return True, "TAKE_PROFIT"
        if price <= trade["sl_price"]:
            log.info(f"🛑 [{label}] SL hit: {symbol} | {pct:.2f}%")
            return True, "STOP_LOSS"
        log.info(f"👀 [{label}] Holding {symbol} | {pct:+.2f}% | Price: {price:.6f}")
        return False, ""

    # ── Live mode — check exchange order status in ONE call ──────
    open_ids = get_open_order_ids(symbol)

    # If TP order is no longer open → it filled (or was cancelled externally)
    if tp_order_id and tp_order_id not in open_ids:
        log.info(f"🎯 [{label}] TP order filled: {symbol}")
        if sl_order_id and sl_order_id in open_ids:
            cancel_order(symbol, sl_order_id, label)
        return True, "TAKE_PROFIT"

    # If SL order is no longer open → it filled
    if sl_order_id and sl_order_id not in open_ids:
        log.info(f"🛑 [{label}] SL order filled: {symbol}")
        if tp_order_id and tp_order_id in open_ids:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # Both orders still open — log current price for visibility
    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
        pct   = (price - trade["entry_price"]) / trade["entry_price"] * 100
        log.info(f"👀 [{label}] Holding {symbol} | {pct:+.2f}% | TP/SL on exchange")
    except:
        log.info(f"👀 [{label}] Holding {symbol} | TP/SL on exchange")

    return False, ""


def close_position(trade, reason):
    label  = trade["label"]
    symbol = trade["symbol"]

    # TIMEOUT: limit orders already cancelled in check_exit, now market sell
    if reason == "TIMEOUT" and not PAPER_TRADE:
        params = {"symbol": symbol, "side": "SELL", "type": "MARKET", "quantity": trade["qty"]}
        try:
            result = private_post("/api/v3/order", params)
            log.info(f"✅ [{label}] Timeout market sell: {result}")
        except requests.exceptions.HTTPError as e:
            try:    error_body = e.response.json()
            except: error_body = e.response.text if e.response else "no response"
            log.error(f"🚨 [{label}] Timeout market sell failed: {error_body}")
            telegram(f"🚨 <b>Timeout sell failed!</b> [{label}]\n{symbol} — close manually on MEXC.")
            return False

    try:
        exit_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except:
        exit_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]

    pnl_pct  = (exit_price - trade["entry_price"]) / trade["entry_price"] * 100
    pnl_usdt = (exit_price - trade["entry_price"]) * trade["qty"]

    # Strip internal keys before storing
    stored = {k: v for k, v in trade.items() if not k.startswith("_")}
    trade_history.append({
        **stored,
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
    icons     = {"TAKE_PROFIT": ("🎯","Take Profit Hit"),
                 "STOP_LOSS":   ("🛑","Stop Loss Hit"),
                 "TIMEOUT":     ("⏰","Timeout Exit")}
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
    return True

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
        f"Trades today: {trades_today}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"<i>/pnl — weekly P&L  |  /status — open trades</i>"
    )


def send_daily_summary(balance: float):
    global last_daily_summary
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if last_daily_summary == today or datetime.now(timezone.utc).hour != 0:
        return
    last_daily_summary = today

    mode = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    if PAPER_TRADE:
        if not trade_history:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today. Still scanning.")
            return
        def block(label):
            trades = [t for t in trade_history if t.get("label") == label]
            if not trades: return ""
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
        return

    try:
        now_ms   = int(time.time() * 1000)
        start_ms = now_ms - 86400_000
        symbols  = get_traded_symbols(start_ms)

        if not symbols:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today. Still scanning.")
            return

        data = fetch_mexc_trades_for_symbols(symbols, start_ms)
        if not data:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today. Still scanning.")
            return

        orders = defaultdict(lambda: {"symbol":"","qty":0,"cost":0,"side":"","time":0})
        for fill in data:
            oid = fill["orderId"]
            orders[oid]["symbol"] = fill["symbol"]
            orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
            orders[oid]["time"]   = fill["time"]
            orders[oid]["qty"]   += float(fill["qty"])
            orders[oid]["cost"]  += float(fill["quoteQty"])

        buys  = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells = {o: v for o, v in orders.items() if v["side"] == "SELL"}

        if not buys and not sells:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today. Still scanning.")
            return

        total_bought = sum(v["cost"] for v in buys.values())
        total_sold   = sum(v["cost"] for v in sells.values())
        net_pnl      = round(total_sold - total_bought, 4)
        pnl_emoji    = "📈" if net_pnl >= 0 else "📉"
        symbols      = sorted(set(v["symbol"] for v in orders.values()))
        sym_str      = ", ".join(symbols) if len(symbols) <= 5 else f"{len(symbols)} pairs"

        telegram(
            f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
            f"Orders:       <b>{len(buys)} buys / {len(sells)} sells</b>\n"
            f"Pairs:        <b>{sym_str}</b>\n"
            f"Total bought: <b>${total_bought:,.2f} USDT</b>\n"
            f"Total sold:   <b>${total_sold:,.2f} USDT</b>\n"
            f"Net P&L:      {pnl_emoji} <b>${net_pnl:+.2f} USDT</b>\n"
            f"━━━━━━━━━━━━━━━\nBalance: <b>${balance:.2f} USDT</b>"
        )
    except Exception as e:
        log.error(f"Daily summary failed: {e}")
        telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nCould not fetch: {str(e)[:200]}")

def fetch_mexc_trades_for_symbols(symbols: list, start_ms: int) -> list:
    """
    Fetch trades for a list of symbols. MEXC requires symbol param on myTrades.
    Returns combined list of fills across all symbols.
    """
    all_fills = []
    for sym in symbols:
        try:
            fills = private_get("/api/v3/myTrades", {
                "symbol":    sym,
                "startTime": start_ms,
                "limit":     1000,
            })
            if fills:
                all_fills.extend(fills)
        except Exception as e:
            log.debug(f"myTrades fetch failed for {sym}: {e}")
        time.sleep(0.1)
    return all_fills


def get_traded_symbols(start_ms: int) -> list:
    """
    Return symbols we've traded in the current session (from trade_history).
    Falls back to a hardcoded list of common pairs if history is empty.
    """
    session_symbols = list({t["symbol"] for t in trade_history})
    if session_symbols:
        return session_symbols
    # No history yet (e.g. bot just started) — return empty, P&L will show 0
    return []

def fetch_mexc_weekly_pnl() -> dict:
    if PAPER_TRADE:
        week_ago    = datetime.now(timezone.utc).timestamp() - 7 * 86400
        week_trades = [t for t in trade_history
                       if datetime.fromisoformat(t.get("closed_at","1970-01-01")).timestamp() >= week_ago]
        wins   = [t for t in week_trades if t["pnl_pct"] > 0]
        losses = [t for t in week_trades if t["pnl_pct"] <= 0]
        return {
            "total":    len(week_trades), "wins": len(wins), "losses": len(losses),
            "pnl_usdt": round(sum(t["pnl_usdt"] for t in week_trades), 4),
            "best":     max(week_trades, key=lambda t: t["pnl_pct"]) if week_trades else None,
            "worst":    min(week_trades, key=lambda t: t["pnl_pct"]) if week_trades else None,
        }
    try:
        now_ms   = int(time.time() * 1000)
        start_ms = now_ms - 7 * 86400_000
        symbols  = get_traded_symbols(start_ms)

        if not symbols:
            return {"total": 0, "buys": 0, "sells": 0,
                    "pnl_usdt": 0.0, "total_bought": 0.0, "total_sold": 0.0,
                    "note": "No trades recorded this session yet."}

        data = fetch_mexc_trades_for_symbols(symbols, start_ms)
        if not data:
            return {"error": "No fills found for traded symbols"}

        orders = defaultdict(lambda: {"symbol":"","qty":0,"cost":0,"side":""})
        for fill in data:
            oid = fill["orderId"]
            orders[oid]["symbol"] = fill["symbol"]
            orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
            orders[oid]["qty"]   += float(fill["qty"])
            orders[oid]["cost"]  += float(fill["quoteQty"])

        buys  = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells = {o: v for o, v in orders.items() if v["side"] == "SELL"}
        total_bought = sum(v["cost"] for v in buys.values())
        total_sold   = sum(v["cost"] for v in sells.values())
        buy_syms     = Counter(v["symbol"] for v in buys.values())
        sell_syms    = Counter(v["symbol"] for v in sells.values())
        completed    = sum(min(buy_syms[s], sell_syms[s]) for s in buy_syms)

        return {
            "total": completed, "buys": len(buys), "sells": len(sells),
            "pnl_usdt": round(total_sold - total_bought, 4),
            "total_bought": round(total_bought, 2), "total_sold": round(total_sold, 2),
        }
    except Exception as e:
        log.error(f"Weekly P&L fetch failed: {e}")
        return {"error": str(e)}


def build_weekly_message(pnl: dict, balance: float) -> str:
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    pnl_emoji = "📈" if pnl.get("pnl_usdt", 0) >= 0 else "📉"
    if "error" in pnl:
        return f"📊 <b>Weekly P&L</b> [{mode}]\n━━━━━━━━━━━━━━━\nCould not fetch: {pnl['error']}"
    if PAPER_TRADE:
        win_rate = f"{pnl['wins']/pnl['total']*100:.0f}%" if pnl.get("total") else "n/a"
        msg = (f"{pnl_emoji} <b>Weekly Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
               f"Trades:   <b>{pnl['total']}</b>  ({pnl.get('wins',0)}W / {pnl.get('losses',0)}L)\n"
               f"Win rate: <b>{win_rate}</b>\n"
               f"P&L:      <b>${pnl['pnl_usdt']:+.2f} USDT</b>\n"
               f"Balance:  <b>${balance:.2f} USDT</b>")
        if pnl.get("best"):  msg += f"\nBest:  {pnl['best']['symbol']} {pnl['best']['pnl_pct']:+.2f}%"
        if pnl.get("worst"): msg += f"\nWorst: {pnl['worst']['symbol']} {pnl['worst']['pnl_pct']:+.2f}%"
        return msg
    return (f"{pnl_emoji} <b>Weekly Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
            f"Round trips:  <b>{pnl['total']}</b>\n"
            f"Total bought: <b>${pnl['total_bought']:,.2f} USDT</b>\n"
            f"Total sold:   <b>${pnl['total_sold']:,.2f} USDT</b>\n"
            f"Net P&L:      <b>${pnl['pnl_usdt']:+.2f} USDT</b>\n"
            f"Balance:      <b>${balance:.2f} USDT</b>")


def send_weekly_summary(balance: float):
    global last_weekly_summary
    now      = datetime.now(timezone.utc)
    week_str = f"{now.isocalendar()[0]}-W{now.isocalendar()[1]:02d}"
    if last_weekly_summary == week_str or now.weekday() != 0 or now.hour != 0:
        return
    last_weekly_summary = week_str
    telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))
    log.info(f"📊 Weekly summary sent for {week_str}")

# ── Telegram command listener ──────────────────────────────────

def listen_for_commands(balance: float):
    global last_telegram_update
    try:
        params = {"timeout": 0, "limit": 5}
        if last_telegram_update:
            params["offset"] = last_telegram_update + 1
        data = requests.get(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
            params=params, timeout=5
        ).json()

        for update in data.get("result", []):
            last_telegram_update = update["update_id"]
            msg  = update.get("message", {})
            text = msg.get("text", "").strip().lower()
            if str(msg.get("chat", {}).get("id")) != str(TELEGRAM_CHAT_ID):
                continue

            if text in ("/pnl", "/pnl@mexcbot"):
                log.info("📊 /pnl command received")
                telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))

            elif text in ("/status", "/status@mexcbot"):
                log.info("📋 /status command received")
                mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
                lines = [f"📋 <b>Status</b> [{mode}]\n━━━━━━━━━━━━━━━"]
                for t, name in [(scalper_trade, "Scalper"), (alt_trade, "Alt")]:
                    if t:
                        try:
                            price = float(public_get("/api/v3/ticker/price",
                                                     {"symbol": t["symbol"]})["price"])
                            pct = (price - t["entry_price"]) / t["entry_price"] * 100
                            lines.append(f"{name}: <b>{t['symbol']}</b> | {pct:+.2f}% | "
                                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
                        except:
                            lines.append(f"{name}: <b>{t['symbol']}</b> (price unavailable)")
                    else:
                        lines.append(f"{name}: scanning...")
                lines.append(f"Balance: <b>${balance:.2f} USDT</b>")
                telegram("\n".join(lines))

    except Exception as e:
        log.debug(f"Telegram poll error: {e}")

# ── Main loop ──────────────────────────────────────────────────

def run():
    global scalper_trade, alt_trade

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")
    log.info(f"   Scalper : TP {SCALPER_TP*100}% / SL {SCALPER_SL*100}% / RSI max {SCALPER_MAX_RSI}")
    log.info(f"   Moonshot: TP {MOONSHOT_TP*100}% / SL {MOONSHOT_SL*100}% / max {MOONSHOT_MAX_HOURS}h")
    log.info(f"   Reversal: TP {REVERSAL_TP*100}% / SL {REVERSAL_SL*100}% / max {REVERSAL_MAX_HOURS}h")

    _load_symbol_rules()

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
        f"  TP: +{REVERSAL_TP*100:.0f}%  |  SL: -{REVERSAL_SL*100:.0f}%  |  max {REVERSAL_MAX_HOURS}h\n"
        f"\n<i>Commands: /pnl — weekly P&L | /status — current trades</i>"
    )

    scalper_excluded = None
    alt_excluded     = None

    while True:
        try:
            balance = get_available_balance()
            _load_symbol_rules()

            open_symbols = {t["symbol"] for t in [scalper_trade, alt_trade] if t}
            tickers      = fetch_tickers() if (scalper_trade is None or alt_trade is None) else None

            # ── Scalper leg ───────────────────────────────────────
            if scalper_trade is None:
                budget = round(balance * SCALPER_BUDGET_PCT, 2)
                opp    = find_scalper_opportunity(tickers, budget,
                                                  exclude=scalper_excluded,
                                                  open_symbols=open_symbols)
                if opp:
                    scalper_trade    = open_position(opp, budget, SCALPER_TP, SCALPER_SL, "SCALPER")
                    scalper_excluded = None
            else:
                should_exit, reason = check_exit(scalper_trade)
                if should_exit:
                    scalper_excluded = scalper_trade["symbol"]
                    if close_position(scalper_trade, reason):
                        scalper_trade = None
                        log.info("🔄 [SCALPER] Closed. Re-scanning next cycle...")

            # ── Alt leg (Moonshot OR Reversal) ────────────────────
            if alt_trade is None:
                budget = round(balance * MOONSHOT_BUDGET_PCT, 2)
                opp    = find_moonshot_opportunity(tickers, budget,
                                                   exclude=alt_excluded,
                                                   open_symbols=open_symbols)
                if opp:
                    alt_trade    = open_position(opp, budget, MOONSHOT_TP, MOONSHOT_SL,
                                                 "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                    alt_excluded = None
                else:
                    opp = find_reversal_opportunity(tickers, budget,
                                                    exclude=alt_excluded,
                                                    open_symbols=open_symbols)
                    if opp:
                        alt_trade    = open_position(opp, budget, REVERSAL_TP, REVERSAL_SL,
                                                     "REVERSAL", max_hours=REVERSAL_MAX_HOURS)
                        alt_excluded = None
            else:
                should_exit, reason = check_exit(alt_trade)
                if should_exit:
                    closed_label = alt_trade["label"]
                    alt_excluded = alt_trade["symbol"]
                    if close_position(alt_trade, reason):
                        alt_trade = None
                        log.info(f"🔄 [{closed_label}] Closed. Re-scanning next cycle...")

            send_heartbeat(balance)
            send_daily_summary(balance)
            send_weekly_summary(balance)
            listen_for_commands(balance)
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
