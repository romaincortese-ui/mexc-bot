"""
MEXC Trading Bot — 3 Strategies
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER  — Max 3 trades (30% each) | Trailing Stop | ATR SL | 1H trend aligned
  2. MOONSHOT — 1 trade (5%) | TP +12% | SL -10% | 1H momentum + new listings
  3. REVERSAL — 1 trade (5%) | TP +3%  | SL -2%  | Oversold bounce + volume capitulation
     Moonshot and Reversal share the 5% slot.
"""

import time, hmac, hashlib, logging, requests, math
import urllib.parse
import pandas as pd
import numpy as np
from collections import defaultdict, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = "mx0vglg1LIlEl98JhQ"
MEXC_API_SECRET = "2b53b21288c8494bbec5e0cc7f34d8c2"

PAPER_TRADE   = False
PAPER_BALANCE = 50.0

# ── Scalper (max 3 concurrent) ────────────────────────────────
SCALPER_MAX_TRADES  = 3
SCALPER_BUDGET_PCT  = 0.30      # 30% per trade
SCALPER_TP_LIMIT    = 0.10      # +10% — exchange limit order
SCALPER_TRAIL_ACT   = 0.02      # trailing stop activates at +2%
SCALPER_TRAIL_PCT   = 0.01      # trail 1% below highest price
SCALPER_ATR_MULT    = 1.5       # SL = 1.5 × ATR
SCALPER_SL          = 0.02      # fallback SL if ATR unavailable (2%)
SCALPER_FLAT_MINS   = 30        # exit flat trade after 30min
SCALPER_FLAT_RANGE  = 0.005     # ±0.5% = flat
SCALPER_ROTATE_GAP  = 20        # rotate worst trade if new opp scores this much higher
SCALPER_MIN_VOL     = 500_000   # min 24h USDT volume — lowered to widen candidate pool
SCALPER_MIN_PRICE   = 0.01
SCALPER_MIN_CHANGE  = 0.1       # min 24h abs % change — kept low, scoring handles momentum
SCALPER_THRESHOLD   = 20
SCALPER_MAX_RSI     = 70

# ── Moonshot ──────────────────────────────────────────────────
ALT_MAX_TRADES      = 3         # max concurrent moonshot/reversal trades
MOONSHOT_BUDGET_PCT = 0.05
MOONSHOT_TP         = 0.12
MOONSHOT_SL         = 0.10
MOONSHOT_MAX_VOL    = 500_000
MOONSHOT_MIN_VOL    = 5_000
MOONSHOT_MIN_1H     = 5.0
MOONSHOT_THRESHOLD  = 15
MOONSHOT_MAX_HOURS  = 1
MOONSHOT_MIN_DAYS   = 2         # skip listings < 48h old (too volatile)
MOONSHOT_NEW_DAYS   = 14        # listings < 14 days = "new"

# ── Reversal ──────────────────────────────────────────────────
REVERSAL_BUDGET_PCT = 0.05
REVERSAL_TP         = 0.030
REVERSAL_SL         = 0.020
REVERSAL_MIN_VOL    = 100_000
REVERSAL_MAX_RSI    = 32
REVERSAL_MIN_DROP   = 3.0
REVERSAL_MAX_HOURS  = 4

# ── Shared ────────────────────────────────────────────────────
MIN_PRICE     = 0.001
SCAN_INTERVAL = 60

TELEGRAM_TOKEN   = "8729639207:AAGR2ytuX36ocCVagQj-tGBE2QEkvrTiqQo"
TELEGRAM_CHAT_ID = "7058246374"

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
scalper_trades       = []   # list — up to SCALPER_MAX_TRADES open at once
alt_trades           = []   # list — up to ALT_MAX_TRADES open at once
last_heartbeat_at    = 0
last_daily_summary   = ""
last_weekly_summary  = ""
last_telegram_update = 0
last_top_scalper     = None
last_top_alt         = None

_symbol_rules         = {}
_symbol_rules_fetched = False
_symbol_rules_at      = 0

# Rolling buffer of scanner activity lines for /logs command
# Symbols that returned "not support api" — skip permanently
_api_blacklist: set = set()


_MAX_SCANNER_LOGS     = 5
_paused               = False  # set by /pause command, cleared by /resume

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

def scanner_log(msg: str):
    """Log a scanner activity line and keep it in the rolling buffer for /logs."""
    global _scanner_log_buffer
    global _scanner_log_buffer
    ts  = datetime.now(timezone.utc).strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    log.info(msg)
    _scanner_log_buffer.append(line)
    if len(_scanner_log_buffer) > _MAX_SCANNER_LOGS:
        _scanner_log_buffer.pop(0)

def public_get(path, params=None):
    r = requests.get(BASE_URL + path, params=params or {}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_request(method, path, params=None):
    """Unified signed request using urllib.parse.urlencode for correct encoding."""
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    query_string = urllib.parse.urlencode(params)
    signature    = hmac.new(
        MEXC_API_SECRET.encode("utf-8"),
        query_string.encode("utf-8"),
        hashlib.sha256
    ).hexdigest()
    url     = f"{BASE_URL}{path}?{query_string}&signature={signature}"
    headers = {"X-MEXC-APIKEY": MEXC_API_KEY}
    if   method == "GET":    r = requests.get(url, headers=headers, timeout=10)
    elif method == "POST":   r = requests.post(url, headers=headers, timeout=10)
    elif method == "DELETE": r = requests.delete(url, headers=headers, timeout=10)
    r.raise_for_status()
    return r.json()

def private_get(path, params=None):    return private_request("GET",    path, params)
def private_post(path, params=None):   return private_request("POST",   path, params)
def private_delete(path, params=None): return private_request("DELETE", path, params)

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
            step_size    = 1.0
            min_notional = 1.0
            tick_size    = None
            for f in s.get("filters", []):
                if f["filterType"] == "LOT_SIZE":
                    min_qty   = float(f.get("minQty",   1.0))
                    step_size = float(f.get("stepSize", 1.0))
                if f["filterType"] == "MIN_NOTIONAL":
                    min_notional = float(f.get("minNotional", 1.0))
                if f["filterType"] == "PRICE_FILTER":
                    tick_size = f.get("tickSize")  # kept as string for precision
            _symbol_rules[sym] = {
                "min_qty":      min_qty,
                "step_size":    step_size,
                "min_notional": min_notional,
                "tick_size":    tick_size,
            }
        _symbol_rules_fetched = True
        _symbol_rules_at      = time.time()
        log.info(f"📋 Loaded rules for {len(_symbol_rules)} symbols.")
    except Exception as e:
        log.error(f"Failed to load symbol rules: {e}")

def get_symbol_rules(symbol):
    """Return (min_qty, step_size, min_notional, tick_size)."""
    r = _symbol_rules.get(symbol)
    if r:
        return r["min_qty"], r["step_size"], r["min_notional"], r.get("tick_size")
    return 1.0, 1.0, 1.0, None

def round_price_to_tick(price: float, tick_size: str | None) -> float:
    """Floor price to exchange tick size. Falls back to 8dp if tick unknown."""
    if not tick_size or float(tick_size) == 0:
        return round(price, 8)
    tick_str = tick_size.rstrip("0") or "1"
    decimals = len(tick_str.split(".")[1]) if "." in tick_str else 0
    tick     = float(tick_size)
    return round(int(price / tick) * tick, decimals)

def calc_qty(budget: float, price: float, step_size: float) -> float:
    """Floor qty to nearest valid step using step_size from exchange info."""
    raw     = budget / price
    floored = math.floor(raw / step_size) * step_size
    step_str = str(step_size).rstrip("0")
    decimals = len(step_str.split(".")[1]) if "." in step_str else 0
    return round(floored, decimals)

# ── Balance ────────────────────────────────────────────────────

def get_available_balance() -> float:
    if PAPER_TRADE:
        return round(PAPER_BALANCE + sum(t["pnl_usdt"] for t in trade_history), 2)
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

def calc_atr(df: pd.DataFrame, period=14) -> float:
    """Average True Range — measures volatility for adaptive SL sizing."""
    high       = df["high"]
    low        = df["low"]
    prev_close = df["close"].shift(1)
    tr = pd.concat([
        high - low,
        (high - prev_close).abs(),
        (low  - prev_close).abs(),
    ], axis=1).max(axis=1)
    atr = tr.rolling(period).mean().iloc[-1]
    return float(atr) if not np.isnan(atr) else 0.0

# ── Kline parsing ──────────────────────────────────────────────

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
    try:
        data = public_get("/api/v3/klines", {
            "symbol": symbol, "interval": interval, "limit": limit
        })
        if not data:
            return None
        df = pd.DataFrame(data)
        df.columns = range(len(df.columns))
        df = df.rename(columns={0:"open_time", 1:"open", 2:"high", 3:"low", 4:"close", 5:"volume"})
        for col in ["open", "high", "low", "close", "volume"]:
            df[col] = pd.to_numeric(df[col], errors="coerce")
        df = df.dropna(subset=["close", "volume"])
        return df if len(df) >= min_len else None
    except Exception as e:
        log.info(f"⚠️ Klines error {symbol}: {type(e).__name__}: {e}")
        return None

def fetch_tickers() -> pd.DataFrame:
    data = public_get("/api/v3/ticker/24hr")
    df   = pd.DataFrame(data)
    df   = df[df["symbol"].str.endswith("USDT")].copy()
    for col in ["quoteVolume", "volume", "priceChangePercent", "lastPrice"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    df["abs_change"] = df["priceChangePercent"].abs()
    return df.dropna(subset=["quoteVolume", "lastPrice"])

# ── Notional pre-check ─────────────────────────────────────────

def pick_tradeable(candidates: list, budget: float, label: str) -> dict | None:
    for c in candidates:
        min_qty, step_size, min_notional, _ = get_symbol_rules(c["symbol"])
        qty      = calc_qty(budget, c["price"], step_size)
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

def evaluate_scalper_candidate(sym: str) -> dict | None:
    """
    Score a single scalper candidate.
    Requires 1H trend alignment (price above EMA50 on 1H) before scoring 5m signals.
    Returns dict with score, rsi, price, atr_pct or None if disqualified.
    """
    # 1H trend filter — don't fight the trend
    df_1h = parse_klines(sym, interval="60m", limit=60)
    if df_1h is None:
        return None
    ema50_1h = calc_ema(df_1h["close"], 50).iloc[-1]
    if float(df_1h["close"].iloc[-1]) < ema50_1h:
        return None  # price below 1H EMA50 — downtrend, skip

    df5m = parse_klines(sym, interval="5m", limit=60)
    if df5m is None:
        return None

    close  = df5m["close"]
    volume = df5m["volume"]

    rsi = calc_rsi(close)
    if np.isnan(rsi) or rsi > SCALPER_MAX_RSI:
        return None

    rsi_score = max(0, 40 - rsi) if rsi < 50 else 0

    ema9  = calc_ema(close, 9)
    ema21 = calc_ema(close, 21)
    crossed_up  = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
    trending_up = ema9.iloc[-1] > ema21.iloc[-1]
    ma_score = 30 if crossed_up else (15 if trending_up else 0)

    avg_vol   = volume.iloc[-20:-1].mean()
    vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
    vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0

    score = rsi_score + ma_score + vol_score
    if score < SCALPER_THRESHOLD:
        return None

    atr     = calc_atr(df5m)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    return {
        "symbol":    sym,
        "score":     round(score, 2),
        "rsi":       round(rsi, 2),
        "vol_ratio": round(vol_ratio, 2),
        "price":     float(close.iloc[-1]),
        "atr_pct":   round(atr_pct, 6),
    }


def find_scalper_opportunity(tickers: pd.DataFrame, budget: float,
                              exclude: set, open_symbols: set) -> dict | None:
    global last_top_scalper

    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= SCALPER_MIN_PRICE]
    df = df[df["abs_change"]  >= SCALPER_MIN_CHANGE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(80)["symbol"].tolist()[:40]

    log.info(f"🔍 [SCALPER] Ticker filters: vol≥${SCALPER_MIN_VOL/1e6:.1f}M "
             f"price≥${SCALPER_MIN_PRICE} change≥{SCALPER_MIN_CHANGE}% → {len(candidates)} candidates")

    # Pre-filter new listings (< 7 days) — pump risk
    established = []
    for sym in candidates:
        try:
            data = public_get("/api/v3/klines", {"symbol": sym, "interval": "1d", "limit": 7})
            if len(data) >= 7:
                established.append(sym)
            else:
                log.info(f"[SCALPER] Skip {sym} — new listing ({len(data)} days)")
        except:
            established.append(sym)
        time.sleep(0.05)

    log.info(f"🔍 [SCALPER] Scoring {len(established)} pairs after age filter (parallel)...")
    scores = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(evaluate_scalper_candidate, sym): sym for sym in established}
        for f in as_completed(futures):
            result = f.result()
            if result:
                scores.append(result)

    if not scores:
        scanner_log("🔍 [SCALPER] No qualifying pairs after 1H trend + scoring filters.")
        return None

    scores.sort(key=lambda x: x["score"], reverse=True)
    best = scores[0]
    last_top_scalper = best

    vol_row  = tickers[tickers["symbol"] == best["symbol"]]
    best_vol = float(vol_row["quoteVolume"].iloc[0]) if not vol_row.empty else 0
    scanner_log(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
                f"24h vol: ${best_vol:,.0f} | RSI: {best['rsi']} | "
                f"Vol: {best['vol_ratio']}x | ATR: {best['atr_pct']*100:.2f}%")

    return pick_tradeable(scores, budget, "SCALPER")

# ── Scanner: Moonshot ──────────────────────────────────────────

def get_1h_change(symbol: str) -> float | None:
    try:
        df = parse_klines(symbol, interval="60m", limit=3, min_len=2)
        if df is None:
            return None
        prev = float(df["close"].iloc[-2])
        curr = float(df["close"].iloc[-1])
        return (curr - prev) / prev * 100 if prev > 0 else None
    except:
        return None


def find_new_listings(tickers: pd.DataFrame, exclude: set,
                      open_symbols: set) -> list:
    """Find pairs listed between MOONSHOT_MIN_DAYS and MOONSHOT_NEW_DAYS days ago."""
    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(60)["symbol"].tolist()

    new = []
    for sym in candidates:
        try:
            data = public_get("/api/v3/klines", {
                "symbol": sym, "interval": "1d", "limit": MOONSHOT_NEW_DAYS
            })
            days_old = len(data) if data else 0
            # Skip if too new (< 48h = dump risk) or too old (> MOONSHOT_NEW_DAYS)
            if MOONSHOT_MIN_DAYS <= days_old < MOONSHOT_NEW_DAYS:
                new.append({"symbol": sym, "days_old": days_old})
        except:
            pass
        time.sleep(0.05)

    log.info(f"🌙 [MOONSHOT] Found {len(new)} new listings ({MOONSHOT_MIN_DAYS}-{MOONSHOT_NEW_DAYS} days old)")
    return new


def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float,
                               exclude: set, open_symbols: set) -> dict | None:
    global last_top_alt

    # ── Source 1: 1h momentum movers ─────────────────────────────
    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"] <= MOONSHOT_MAX_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    momentum_candidates = df.sort_values("priceChangePercent", ascending=False).head(40)["symbol"].tolist()

    # ── Source 2: New listings ─────────────────────────────────
    new_listings = find_new_listings(tickers, exclude=exclude, open_symbols=open_symbols)
    new_symbols  = [n["symbol"] for n in new_listings]

    all_candidates = list(dict.fromkeys(new_symbols + momentum_candidates))
    log.info(f"🌙 [MOONSHOT] Scanning {len(all_candidates)} candidates "
             f"({len(new_symbols)} new + {len(momentum_candidates)} momentum)...")

    if not all_candidates:
        return None

    scores = []
    for sym in all_candidates:
        change_1h = get_1h_change(sym)
        is_new    = sym in new_symbols

        if is_new:
            if change_1h is not None and change_1h < 0:
                time.sleep(0.1)
                continue
        else:
            if change_1h is None or change_1h < MOONSHOT_MIN_1H:
                time.sleep(0.1)
                continue

        interval = "1h" if is_new else "15m"
        df_k     = parse_klines(sym, interval=interval, limit=60)
        if df_k is None:
            time.sleep(0.1)
            continue

        close  = df_k["close"]
        volume = df_k["volume"]
        rsi    = calc_rsi(close)
        if np.isnan(rsi):
            time.sleep(0.1)
            continue

        rsi_score = max(0, 40 - rsi) if rsi < 50 else 0
        ema9  = calc_ema(close, 9)
        ema21 = calc_ema(close, 21)
        crossed_up  = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        ma_score    = 30 if crossed_up else (15 if ema9.iloc[-1] > ema21.iloc[-1] else 0)
        avg_vol     = volume.iloc[-20:-1].mean()
        vol_ratio   = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        vol_score   = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
        score       = rsi_score + ma_score + vol_score

        if score >= MOONSHOT_THRESHOLD:
            scores.append({
                "symbol": sym, "score": round(score, 2), "rsi": round(rsi, 2),
                "vol_ratio": round(vol_ratio, 2), "price": float(close.iloc[-1]),
                "_df": df_k, "_is_new": is_new, "_1h_chg": round(change_1h or 0, 2),
            })
        time.sleep(0.1)

    if not scores:
        scanner_log("🌙 [MOONSHOT] No qualifying candidates.")
        return None

    scores.sort(key=lambda x: x["score"] + (5 if x.get("_is_new") else 0), reverse=True)
    best = scores[0]
    last_top_alt = best
    scanner_log(f"🌙 [MOONSHOT] Top: {best['symbol']}{'🆕' if best.get('_is_new') else ''} | "
                f"Score: {best['score']}/100 | 1h: {best['_1h_chg']:+.1f}% | RSI: {best['rsi']}")

    tradeable = []
    for s in scores:
        df_k   = s.pop("_df", None)
        is_new = s.pop("_is_new", False)
        s.pop("_1h_chg", None)
        if df_k is None or len(df_k) < 6:
            tradeable.append(s)
            continue

        close  = df_k["close"]
        volume = df_k["volume"]
        opens  = df_k["open"]
        avg_vol     = volume.iloc[-11:-1].mean()
        vol_burst   = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        candle_moves= (close - opens).abs() / opens * 100
        avg_move    = candle_moves.iloc[-11:-1].mean()
        price_burst = (float(candle_moves.iloc[-1]) / avg_move) if avg_move > 0 else 1.0
        greens      = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])

        vol_thresh   = 2.0 if is_new else 3.0
        price_thresh = 1.5 if is_new else 2.0

        if vol_burst < vol_thresh and price_burst < price_thresh:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — no burst")
            continue
        if greens == 0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — both candles red")
            continue
        tradeable.append(s)

    if not tradeable:
        log.info("[MOONSHOT] No pairs passed burst check.")
        return None

    return pick_tradeable(tradeable, budget, "MOONSHOT")

# ── Scanner: Reversal ──────────────────────────────────────────

def evaluate_reversal_candidate(sym: str) -> dict | None:
    """
    Score a reversal candidate.
    Requires: RSI < 32, current candle green, prior red candle had capitulation volume (1.5x avg).
    """
    df5m = parse_klines(sym, interval="5m", limit=60, min_len=30)
    if df5m is None:
        return None

    # Current candle must be green — bounce has started
    if float(df5m["close"].iloc[-1]) <= float(df5m["open"].iloc[-1]):
        return None

    # Prior candle must have capitulation volume (selling exhaustion)
    volume    = df5m["volume"]
    avg_vol   = float(volume.iloc[-20:-2].mean())
    prev_vol  = float(volume.iloc[-2])
    if avg_vol > 0 and prev_vol < avg_vol * 1.5:
        return None  # no volume capitulation on the red candle

    rsi = calc_rsi(df5m["close"])
    if np.isnan(rsi) or rsi > REVERSAL_MAX_RSI:
        return None

    return {
        "symbol": sym,
        "price":  float(df5m["close"].iloc[-1]),
        "rsi":    round(rsi, 2),
        "score":  round(rsi, 2),  # lower RSI = better reversal candidate
    }


def find_reversal_opportunity(tickers: pd.DataFrame, budget: float,
                               exclude: set, open_symbols: set) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"]        >= REVERSAL_MIN_VOL]
    df = df[df["lastPrice"]          >= MIN_PRICE]
    df = df[df["priceChangePercent"] <= -REVERSAL_MIN_DROP]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    candidates = df.sort_values("priceChangePercent", ascending=True).head(30)["symbol"].tolist()

    log.info(f"🔄 [REVERSAL] Scoring {len(candidates)} oversold pairs (parallel)...")
    if not candidates:
        return None

    tradeable = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(evaluate_reversal_candidate, sym): sym for sym in candidates}
        for f in as_completed(futures):
            result = f.result()
            if result:
                tradeable.append(result)

    if not tradeable:
        scanner_log("[REVERSAL] No oversold pairs with capitulation + green candle.")
        return None

    tradeable.sort(key=lambda x: x["rsi"])  # most oversold first
    best = tradeable[0]
    last_top_alt = best
    scanner_log(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | Price: {best['price']}")

    return pick_tradeable(tradeable, budget, "REVERSAL")

# ── Order execution ────────────────────────────────────────────

def place_market_buy(symbol, qty, label=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] BUY {qty} {symbol} @ MARKET")
        return {"orderId": f"PAPER_BUY_{int(time.time())}"}
    try:
        result = private_post("/api/v3/order", {
            "symbol": symbol, "side": "BUY", "type": "MARKET", "quantity": str(qty)
        })
        log.info(f"✅ [{label}] BUY placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:    error_body = e.response.json()
        except: error_body = e.response.text if e.response else "no response"
        # Code 10007 = symbol not API-tradeable — blacklist permanently
        if isinstance(error_body, dict) and error_body.get("code") == 10007:
            _api_blacklist.add(symbol)
            log.warning(f"⚠️ [{label}] {symbol} not API-tradeable — blacklisted.")
        else:
            log.error(f"🚨 [{label}] BUY rejected: {error_body}")
            telegram(f"🚨 <b>BUY rejected</b> [{label}]\n{symbol} qty={qty}\nReason: {str(error_body)[:300]}")
        return None


def place_limit_sell(symbol, qty, price, label="", tag=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] LIMIT SELL {qty} {symbol} @ {price} ({tag})")
        return f"PAPER_{tag}_{int(time.time())}"
    try:
        result   = private_post("/api/v3/order", {
            "symbol": symbol, "side": "SELL", "type": "LIMIT",
            "quantity": str(qty), "price": str(price)
        })
        order_id = result.get("orderId")
        log.info(f"✅ [{label}] LIMIT SELL ({tag}): {order_id} @ {price}")
        return order_id
    except requests.exceptions.HTTPError as e:
        try:    error_body = e.response.json()
        except: error_body = e.response.text if e.response else "no response"
        log.error(f"🚨 [{label}] LIMIT SELL rejected ({tag}): {error_body}")
        return None


def cancel_order(symbol, order_id, label=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] Cancel {order_id}")
        return
    try:
        private_delete("/api/v3/order", {"symbol": symbol, "orderId": order_id})
        log.info(f"✅ [{label}] Cancelled {order_id}")
    except Exception as e:
        log.debug(f"[{label}] Cancel {order_id} failed (may already be filled): {e}")


def get_open_order_ids(symbol) -> set:
    if PAPER_TRADE:
        return set()
    try:
        orders = private_get("/api/v3/openOrders", {"symbol": symbol})
        return {o["orderId"] for o in orders}
    except Exception as e:
        log.debug(f"get_open_order_ids error {symbol}: {e}")
        return set()

# ── Trade lifecycle ────────────────────────────────────────────

def open_position(opp, budget_usdt, tp_pct, sl_pct, label,
                  max_hours=None, sl_override_pct=None):
    symbol                           = opp["symbol"]
    min_qty, step_size, min_notional, tick_size = get_symbol_rules(symbol)

    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.warning(f"[{label}] Fresh price failed, using scored price: {e}")
        price = opp["price"]

    qty      = calc_qty(budget_usdt, price, step_size)
    notional = round(qty * price, 4)

    if qty < min_qty:
        log.warning(f"[{label}] {symbol} qty {qty} < min {min_qty}, skipping.")
        return None
    if notional < min_notional:
        log.warning(f"[{label}] {symbol} notional ${notional:.2f} < min ${min_notional:.2f}, skipping.")
        return None

    buy_order = place_market_buy(symbol, qty, label)
    if not buy_order:
        return None

    # Use ATR-based SL if provided (scalper), else fixed pct (moonshot/reversal)
    actual_sl_pct = sl_override_pct if sl_override_pct else sl_pct
    tp_price      = round_price_to_tick(price * (1 + tp_pct), tick_size)
    sl_price      = round(price * (1 - actual_sl_pct), 8)

    tp_order_id = place_limit_sell(symbol, qty, tp_price, label, tag="TP")
    if not PAPER_TRADE and not tp_order_id:
        log.warning(f"[{label}] TP limit failed — monitoring manually.")
        telegram(f"⚠️ [{label}] TP limit order failed for {symbol} — monitoring manually.")

    trade = {
        "label":         label,
        "symbol":        symbol,
        "entry_price":   price,
        "qty":           qty,
        "budget_used":   notional,
        "tp_price":      tp_price,
        "sl_price":      sl_price,
        "tp_pct":        tp_pct,
        "sl_pct":        actual_sl_pct,
        "tp_order_id":   tp_order_id,
        "highest_price": price,   # tracked for trailing stop
        "max_hours":     max_hours,
        "opened_at":     datetime.now(timezone.utc).isoformat(),
        "score":         opp.get("score", 0),
        "rsi":           opp.get("rsi", 0),
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons        = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄"}
    icon         = icons.get(label, "🟢")
    timeout_line = f"Max hold:    {max_hours}h\n" if max_hours else ""
    tp_status    = "TP ✅ on exchange" if tp_order_id else "TP monitored by bot"

    log.info(f"{icon} [{label}] Opened {symbol} | ${notional:.2f} | "
             f"Entry: {price:.6f} | TP: {tp_price:.6f} | SL: {sl_price:.6f} (-{actual_sl_pct*100:.1f}%)")
    telegram(
        f"{icon} <b>Trade Opened — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${notional:.2f} USDT</b>\n"
        f"Entry:       <b>${price:.6f}</b>\n"
        f"Take profit: <b>${tp_price:.6f}</b>  (+{tp_pct*100:.0f}%)\n"
        f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl_pct*100:.1f}%) [market]\n"
        f"{timeout_line}"
        f"{tp_status}\n"
        f"Score: {opp.get('score',0)} | RSI: {opp.get('rsi','?')} | Vol: {opp.get('vol_ratio','?')}x"
    )
    return trade


def check_exit(trade, best_score: float = 0) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")

    # ── Timeout ───────────────────────────────────────────────────
    if trade.get("max_hours"):
        hours_held = (datetime.now(timezone.utc) -
                      datetime.fromisoformat(trade["opened_at"])).total_seconds() / 3600
        if hours_held >= trade["max_hours"]:
            log.info(f"⏰ [{label}] Timeout ({trade['max_hours']}h): {symbol}")
            if not PAPER_TRADE and tp_order_id:
                cancel_order(symbol, tp_order_id, label)
            return True, "TIMEOUT"

    # ── Fetch current price ───────────────────────────────────────
    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.error(f"Price fetch error for {symbol}: {e}")
        return False, ""

    pct       = (price - trade["entry_price"]) / trade["entry_price"] * 100
    mins_held = (datetime.now(timezone.utc) -
                 datetime.fromisoformat(trade["opened_at"])).total_seconds() / 60

    # Update highest price for trailing stop
    trade["highest_price"] = max(trade.get("highest_price", price), price)

    # ── Hard safety SL at -5% ────────────────────────────────────
    if pct <= -5.0:
        log.info(f"🚨 [{label}] Hard safety SL: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # ── Normal SL ─────────────────────────────────────────────────
    if price <= trade["sl_price"]:
        log.info(f"🛑 [{label}] SL hit: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # ── TP: exchange limit (live) or price poll (paper/fallback) ──
    if not PAPER_TRADE and tp_order_id:
        open_ids = get_open_order_ids(symbol)
        if tp_order_id not in open_ids:
            log.info(f"🎯 [{label}] TP limit filled: {symbol}")
            return True, "TAKE_PROFIT"
    if PAPER_TRADE or not tp_order_id:
        if price >= trade["tp_price"]:
            log.info(f"🎯 [{label}] TP hit: {symbol} | +{pct:.2f}%")
            return True, "TAKE_PROFIT"

    # ── SCALPER-specific exits ────────────────────────────────────
    if label == "SCALPER":
        # Trailing stop: activates at +2%, trails 1% below highest
        activation = trade["entry_price"] * (1 + SCALPER_TRAIL_ACT)
        if trade["highest_price"] >= activation:
            trail_stop = trade["highest_price"] * (1 - SCALPER_TRAIL_PCT)
            if price <= trail_stop:
                log.info(f"📉 [{label}] Trailing stop: {symbol} | {pct:+.2f}% | "
                         f"High: {((trade['highest_price']/trade['entry_price'])-1)*100:.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TRAILING_STOP"

        # Flat exit: dead money after 30min
        if mins_held >= SCALPER_FLAT_MINS and abs(pct) <= SCALPER_FLAT_RANGE * 100:
            log.info(f"😴 [{label}] Flat exit: {symbol} | {pct:+.2f}% after {mins_held:.0f}min")
            if not PAPER_TRADE and tp_order_id:
                cancel_order(symbol, tp_order_id, label)
            return True, "FLAT_EXIT"

        # Rotation: exit if significantly better opportunity exists and trade isn't winning
        if best_score > 0 and pct < SCALPER_TRAIL_ACT * 100:  # below trailing activation
            score_gap = best_score - trade.get("score", 0)
            if score_gap >= SCALPER_ROTATE_GAP:
                log.info(f"🔀 [{label}] Rotation: {symbol} | {pct:+.2f}% | "
                         f"new opp +{score_gap:.0f}pts better")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "ROTATION"

    log.info(f"👀 [{label}] Holding {symbol} | {pct:+.2f}% | {mins_held:.0f}min | "
             f"High: {((trade['highest_price']/trade['entry_price'])-1)*100:.2f}%")
    return False, ""


def close_position(trade, reason) -> bool:
    label  = trade["label"]
    symbol = trade["symbol"]

    # Market sell for all bot-triggered exits (TP handled by exchange limit)
    needs_sell = reason in ("STOP_LOSS", "TRAILING_STOP", "TIMEOUT", "FLAT_EXIT", "ROTATION")
    if needs_sell and not PAPER_TRADE:
        try:
            result = private_post("/api/v3/order", {
                "symbol": symbol, "side": "SELL", "type": "MARKET",
                "quantity": str(trade["qty"])
            })
            log.info(f"✅ [{label}] Market sell ({reason}): {result}")
        except requests.exceptions.HTTPError as e:
            try:    error_body = e.response.json()
            except: error_body = e.response.text if e.response else "no response"
            log.error(f"🚨 [{label}] Market sell failed: {error_body}")
            telegram(f"🚨 <b>Sell failed!</b> [{label}] {symbol} ({reason})\nClose manually on MEXC.")
            return False

    try:
        exit_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except:
        exit_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]

    pnl_pct  = (exit_price - trade["entry_price"]) / trade["entry_price"] * 100
    pnl_usdt = (exit_price - trade["entry_price"]) * trade["qty"]

    trade_history.append({
        **{k: v for k, v in trade.items() if not k.startswith("_")},
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
    icons     = {
        "TAKE_PROFIT":   ("🎯", "Take Profit Hit"),
        "STOP_LOSS":     ("🛑", "Stop Loss Hit"),
        "TRAILING_STOP": ("📉", "Trailing Stop Hit"),
        "FLAT_EXIT":     ("😴", "Flat Exit"),
        "ROTATION":      ("🔀", "Rotated to Better Trade"),
        "TIMEOUT":       ("⏰", "Timeout Exit"),
    }
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
    log.info(f"📈 Closed {symbol} [{reason}] {pnl_pct:+.2f}% | "
             f"Win rate: {win_rate:.0f}% | Total P&L: ${total_pnl:+.2f}")
    return True

# ── Heartbeat ─────────────────────────────────────────────────

def send_heartbeat(balance: float):
    global last_heartbeat_at
    if time.time() - last_heartbeat_at < 3600:
        return
    last_heartbeat_at = time.time()

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    today        = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trades_today = len([t for t in trade_history if t.get("closed_at","")[:10] == today])

    # Scalper lines — one per open trade
    scalper_lines = []
    for t in scalper_trades:
        try:
            px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            scalper_lines.append(f"  🟢 {t['symbol']} {pct:+.2f}%")
        except:
            scalper_lines.append(f"  🟢 {t['symbol']} (price unavailable)")
    if not scalper_trades:
        if last_top_scalper:
            scalper_lines.append(f"  Watching: {last_top_scalper['symbol']} (score {last_top_scalper['score']})")
        else:
            scalper_lines.append("  Scanning...")

    alt_line = ""
    if alt_trades:
        lines = []
        for t in alt_trades:
            try:
                px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
                pct = (px - t["entry_price"]) / t["entry_price"] * 100
                lines.append(f"  {t['label']}: <b>{t['symbol']}</b> {pct:+.2f}%")
            except:
                lines.append(f"  {t['label']}: <b>{t['symbol']}</b>")
        alt_line = "\n".join(lines)
    elif last_top_alt:
        alt_line = f"ALT watching: <b>{last_top_alt['symbol']}</b> (score {last_top_alt['score']})"
    else:
        alt_line = "ALT: scanning..."

    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance:  <b>${balance:.2f} USDT</b>\n"
        f"Scalpers ({len(scalper_trades)}/{SCALPER_MAX_TRADES}):\n"
        + "\n".join(scalper_lines) + "\n"
        f"Alt ({len(alt_trades)}/{ALT_MAX_TRADES}):\n"
        + alt_line + "\n"
        f"Trades today: {trades_today}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"<i>/pnl — weekly P&L  |  /status — open trades</i>"
    )

# ── Daily summary ─────────────────────────────────────────────

def send_daily_summary(balance: float):
    global last_daily_summary
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if last_daily_summary == today or datetime.now(timezone.utc).hour != 0:
        return
    last_daily_summary = today

    mode = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    if PAPER_TRADE:
        if not trade_history:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return
        def block(lbl):
            trades = [t for t in trade_history if t.get("label") == lbl]
            if not trades: return ""
            wins = [t for t in trades if t["pnl_pct"] > 0]
            return (f"\n<b>{lbl}</b>: {len(trades)} trades | "
                    f"Win rate: {len(wins)/len(trades)*100:.0f}% | "
                    f"P&L: ${sum(t['pnl_usdt'] for t in trades):+.2f}")
        total_pnl = sum(t["pnl_usdt"] for t in trade_history)
        telegram(
            f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━"
            + block("SCALPER") + block("MOONSHOT") + block("REVERSAL")
            + f"\n━━━━━━━━━━━━━━━\nTotal P&L: <b>${total_pnl:+.2f}</b>\nBalance: <b>${balance:.2f}</b>"
        )
        return

    try:
        now_ms   = int(time.time() * 1000)
        symbols  = list({t["symbol"] for t in trade_history})
        if not symbols:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return

        all_fills = []
        for sym in symbols:
            try:
                fills = private_get("/api/v3/myTrades", {
                    "symbol": sym, "startTime": now_ms - 86400_000, "limit": 1000
                })
                if fills: all_fills.extend(fills)
            except: pass
            time.sleep(0.1)

        if not all_fills:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return

        orders = defaultdict(lambda: {"symbol":"","qty":0,"cost":0,"side":""})
        for fill in all_fills:
            oid = fill["orderId"]
            orders[oid]["symbol"] = fill["symbol"]
            orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
            orders[oid]["qty"]   += float(fill["qty"])
            orders[oid]["cost"]  += float(fill["quoteQty"])

        buys         = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells        = {o: v for o, v in orders.items() if v["side"] == "SELL"}
        total_bought = sum(v["cost"] for v in buys.values())
        total_sold   = sum(v["cost"] for v in sells.values())
        net_pnl      = round(total_sold - total_bought, 4)
        pnl_emoji    = "📈" if net_pnl >= 0 else "📉"
        sym_str      = ", ".join(sorted({v["symbol"] for v in orders.values()})[:5])

        telegram(
            f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
            f"Orders:  <b>{len(buys)} buys / {len(sells)} sells</b>\n"
            f"Pairs:   <b>{sym_str}</b>\n"
            f"Bought:  <b>${total_bought:,.2f}</b>  Sold: <b>${total_sold:,.2f}</b>\n"
            f"Net P&L: {pnl_emoji} <b>${net_pnl:+.2f} USDT</b>\n"
            f"━━━━━━━━━━━━━━━\nBalance: <b>${balance:.2f} USDT</b>"
        )
    except Exception as e:
        log.error(f"Daily summary failed: {e}")
        telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nCould not fetch: {str(e)[:200]}")

# ── Weekly P&L ────────────────────────────────────────────────

def fetch_mexc_weekly_pnl() -> dict:
    if PAPER_TRADE:
        week_ago    = datetime.now(timezone.utc).timestamp() - 7 * 86400
        week_trades = [t for t in trade_history
                       if datetime.fromisoformat(t.get("closed_at","1970-01-01")).timestamp() >= week_ago]
        wins   = [t for t in week_trades if t["pnl_pct"] > 0]
        losses = [t for t in week_trades if t["pnl_pct"] <= 0]
        return {
            "total": len(week_trades), "wins": len(wins), "losses": len(losses),
            "pnl_usdt": round(sum(t["pnl_usdt"] for t in week_trades), 4),
            "best":  max(week_trades, key=lambda t: t["pnl_pct"]) if week_trades else None,
            "worst": min(week_trades, key=lambda t: t["pnl_pct"]) if week_trades else None,
        }
    try:
        now_ms   = int(time.time() * 1000)
        symbols  = list({t["symbol"] for t in trade_history})
        if not symbols:
            return {"total": 0, "buys": 0, "sells": 0,
                    "pnl_usdt": 0.0, "total_bought": 0.0, "total_sold": 0.0,
                    "note": "No trades this session yet."}

        all_fills = []
        for sym in symbols:
            try:
                fills = private_get("/api/v3/myTrades", {
                    "symbol": sym, "startTime": now_ms - 7*86400_000, "limit": 1000
                })
                if fills: all_fills.extend(fills)
            except: pass
            time.sleep(0.1)

        if not all_fills:
            return {"error": "No fills found for traded symbols"}

        orders = defaultdict(lambda: {"symbol":"","qty":0,"cost":0,"side":""})
        for fill in all_fills:
            oid = fill["orderId"]
            orders[oid]["symbol"] = fill["symbol"]
            orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
            orders[oid]["qty"]   += float(fill["qty"])
            orders[oid]["cost"]  += float(fill["quoteQty"])

        buys         = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells        = {o: v for o, v in orders.items() if v["side"] == "SELL"}
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
            f"Total bought: <b>${pnl['total_bought']:,.2f}</b>\n"
            f"Total sold:   <b>${pnl['total_sold']:,.2f}</b>\n"
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

# ── Telegram commands ─────────────────────────────────────────

def listen_for_commands(balance: float):
    global last_telegram_update, _paused
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
                log.info("📊 /pnl received")
                telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))

            elif text in ("/status", "/status@mexcbot"):
                log.info("📋 /status received")
                mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
                lines = [f"📋 <b>Status</b> [{mode}]\n━━━━━━━━━━━━━━━"]
                for t in scalper_trades:
                    try:
                        px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
                        pct = (px - t["entry_price"]) / t["entry_price"] * 100
                        lines.append(f"🟢 {t['symbol']} | {pct:+.2f}% | "
                                     f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
                    except:
                        lines.append(f"🟢 {t['symbol']} (price unavailable)")
                if not scalper_trades:
                    lines.append("Scalper: scanning...")
                if alt_trades:
                    for t in alt_trades:
                        try:
                            px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
                            pct = (px - t["entry_price"]) / t["entry_price"] * 100
                            lines.append(f"{t['label']}: <b>{t['symbol']}</b> | {pct:+.2f}% | "
                                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
                        except:
                            lines.append(f"{t['label']}: {t['symbol']} (unavailable)")
                else:
                    lines.append("Alt: scanning...")
                lines.append(f"Balance: <b>${balance:.2f} USDT</b>")
                telegram("\n".join(lines))

            elif text in ("/logs", "/logs@mexcbot"):
                log.info("📜 /logs received")
                if _scanner_log_buffer:
                    msg = "📜 <b>Last Scanner Activity</b>\n━━━━━━━━━━━━━━━\n"
                    msg += "\n".join(f"<code>{line}</code>" for line in _scanner_log_buffer)
                else:
                    msg = "📜 <b>Last Scanner Activity</b>\n━━━━━━━━━━━━━━━\nNo scanner activity yet."
                telegram(msg)

            elif text in ("/pause", "/pause@mexcbot"):
                log.info("⏸️ /pause received")
                _paused = True
                telegram(
                    "⏸️ <b>Bot paused.</b>\n"
                    "No new trades will be opened.\n"
                    "Existing positions are still monitored.\n"
                    "Send /resume to restart scanning."
                )

            elif text in ("/resume", "/resume@mexcbot"):
                log.info("▶️ /resume received")
                _paused = False
                telegram("▶️ <b>Bot resumed.</b> Scanning for new trades.")

            elif text in ("/close", "/close@mexcbot"):
                log.info("🚨 /close received — closing all positions")
                telegram("🚨 <b>Emergency close triggered.</b> Closing all open positions...")
                closed = 0
                for t in scalper_trades[:]:
                    if close_position(t, "STOP_LOSS"):
                        scalper_trades.remove(t)
                        closed += 1
                for t in alt_trades[:]:
                    if close_position(t, "STOP_LOSS"):
                        alt_trades.remove(t)
                        closed += 1
                telegram(f"✅ Closed {closed} position(s). Bot will resume scanning.")

            elif text in ("/config", "/config@mexcbot"):
                log.info("⚙️ /config received")
                telegram(
                    f"⚙️ <b>Current Config</b>\n"
                    f"━━━━━━━━━━━━━━━\n"
                    f"🟢 <b>Scalper</b>\n"
                    f"  Max trades: {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%\n"
                    f"  TP limit:   +{SCALPER_TP_LIMIT*100:.0f}%\n"
                    f"  Trail:      +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.0f}% trail\n"
                    f"  ATR SL:     ×{SCALPER_ATR_MULT}\n"
                    f"  Flat exit:  {SCALPER_FLAT_MINS}min ±{SCALPER_FLAT_RANGE*100:.1f}%\n"
                    f"  Min vol:    ${SCALPER_MIN_VOL:,}\n"
                    f"\n🌙 <b>Moonshot</b>\n"
                    f"  TP: +{MOONSHOT_TP*100:.0f}%  SL: -{MOONSHOT_SL*100:.0f}%\n"
                    f"  Max hold: {MOONSHOT_MAX_HOURS}h\n"
                    f"  Min 1h move: {MOONSHOT_MIN_1H}%\n"
                    f"\n🔄 <b>Reversal</b>\n"
                    f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%\n"
                    f"  Max hold: {REVERSAL_MAX_HOURS}h\n"
                    f"  Min drop: {REVERSAL_MIN_DROP}%  Max RSI: {REVERSAL_MAX_RSI}\n"
                    f"\n{'⏸️ PAUSED' if _paused else '▶️ RUNNING'}"
                )

    except Exception as e:
        log.debug(f"Telegram poll error: {e}")

# ── Startup reconciliation ─────────────────────────────────────

def reconcile_open_positions():
    """Check MEXC for open orders at startup — warns if positions are untracked."""
    if PAPER_TRADE:
        return
    try:
        open_orders = private_get("/api/v3/openOrders", {})
        if not open_orders:
            return
        symbols = list({o["symbol"] for o in open_orders})
        log.warning(f"⚠️  Found {len(open_orders)} open orders at startup: {symbols}")
        telegram(
            f"⚠️ <b>Bot restarted with open orders!</b>\n"
            f"━━━━━━━━━━━━━━━\n"
            f"Found {len(open_orders)} open order(s): <b>{', '.join(symbols)}</b>\n\n"
            f"These are likely TP limit orders from before the restart.\n"
            f"SL is no longer active for these positions.\n\n"
            f"👉 Please check MEXC and close any losing positions manually."
        )
    except Exception as e:
        log.error(f"Reconciliation failed: {e}")

# ── Main loop ──────────────────────────────────────────────────

def run():
    global scalper_trades, alt_trades

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")
    log.info(f"   Scalper : Max {SCALPER_MAX_TRADES} trades | TP {SCALPER_TP_LIMIT*100:.0f}% | "
             f"Trail +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.0f}% trail | "
             f"ATR SL ×{SCALPER_ATR_MULT}")
    log.info(f"   Moonshot: TP {MOONSHOT_TP*100:.0f}% / SL {MOONSHOT_SL*100:.0f}% / max {MOONSHOT_MAX_HOURS}h")
    log.info(f"   Reversal: TP {REVERSAL_TP*100:.1f}% / SL {REVERSAL_SL*100:.1f}% / max {REVERSAL_MAX_HOURS}h")

    _load_symbol_rules()
    reconcile_open_positions()

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (max {SCALPER_MAX_TRADES} trades, {SCALPER_BUDGET_PCT*100:.0f}% each)\n"
        f"  TP: +{SCALPER_TP_LIMIT*100:.0f}% limit | Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.0f}%\n"
        f"  SL: ATR ×{SCALPER_ATR_MULT} | 1H trend aligned\n"
        f"\n🌙 <b>Moonshot</b> (max {ALT_MAX_TRADES} trades, 5% each)\n"
        f"  TP: +{MOONSHOT_TP*100:.0f}%  |  SL: -{MOONSHOT_SL*100:.0f}%  |  max {MOONSHOT_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b> (5% | oversold + capitulation)\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  |  SL: -{REVERSAL_SL*100:.1f}%  |  max {REVERSAL_MAX_HOURS}h\n"
        f"\n<i>/status · /pnl · /logs · /config · /pause · /resume · /close</i>"
    )

    scalper_excluded = set()
    alt_excluded     = set()

    while True:
        try:
            balance = get_available_balance()
            _load_symbol_rules()

            open_symbols = {t["symbol"] for t in scalper_trades}
            for t in alt_trades:
                open_symbols.add(t["symbol"])

            # Total account value for smart alt budget
            total_value = balance
            all_open = scalper_trades + alt_trades
            for t in all_open:
                if not PAPER_TRADE:
                    try:
                        px = float(public_get("/api/v3/ticker/price",
                                              {"symbol": t["symbol"]})["price"])
                        total_value += px * t["qty"]
                    except:
                        total_value += t["budget_used"]
                else:
                    total_value += t["budget_used"]

            # Fetch tickers when needed
            need_scan = (not _paused and len(scalper_trades) < SCALPER_MAX_TRADES) or len(alt_trades) < ALT_MAX_TRADES
            tickers   = fetch_tickers() if need_scan else None

            # ── Scalper leg ───────────────────────────────────────
            if not _paused and len(scalper_trades) < SCALPER_MAX_TRADES:
                budget = round(balance * SCALPER_BUDGET_PCT, 2)
                opp    = find_scalper_opportunity(tickers, budget,
                                                  exclude=scalper_excluded,
                                                  open_symbols=open_symbols)
                if opp:
                    sl_atr = opp["atr_pct"] * SCALPER_ATR_MULT
                    trade  = open_position(opp, budget, SCALPER_TP_LIMIT, SCALPER_SL,
                                           "SCALPER", sl_override_pct=sl_atr)
                    if trade:
                        scalper_trades.append(trade)
                        scalper_excluded = set()  # reset exclusions on new entry
            else:
                # At max capacity — scan for rotation opportunity
                # (compare against worst current trade)
                rotation_tickers = tickers if tickers is not None else fetch_tickers()
                budget           = round(balance * SCALPER_BUDGET_PCT, 2)
                best_opp         = find_scalper_opportunity(rotation_tickers, budget,
                                                             exclude=scalper_excluded,
                                                             open_symbols=open_symbols)
                best_score = best_opp["score"] if best_opp else 0

                # Monitor all open scalper trades
                for trade in scalper_trades[:]:
                    # Pass best_score only to worst performer — avoids rotating good trades
                    trade_pct  = (trade.get("highest_price", trade["entry_price"]) /
                                  trade["entry_price"] - 1) * 100
                    worst_pct  = min((t.get("highest_price", t["entry_price"]) /
                                      t["entry_price"] - 1) * 100 for t in scalper_trades)
                    is_worst   = abs(trade_pct - worst_pct) < 0.01
                    score_arg  = best_score if is_worst else 0

                    should_exit, reason = check_exit(trade, best_score=score_arg)
                    if should_exit:
                        scalper_excluded.add(trade["symbol"])
                        if close_position(trade, reason):
                            scalper_trades.remove(trade)
                            if reason == "ROTATION" and best_opp:
                                log.info("🔀 [SCALPER] Entering rotation opportunity...")
                                sl_atr = best_opp["atr_pct"] * SCALPER_ATR_MULT
                                new_t  = open_position(best_opp, budget, SCALPER_TP_LIMIT,
                                                       SCALPER_SL, "SCALPER",
                                                       sl_override_pct=sl_atr)
                                if new_t:
                                    scalper_trades.append(new_t)
                                    scalper_excluded = set()
                            else:
                                log.info(f"🔄 [SCALPER] Closed {trade['symbol']} [{reason}]")

            # ── Alt leg (Moonshot OR Reversal) ────────────────────
            if not _paused and len(alt_trades) < ALT_MAX_TRADES:
                ideal_budget = round(total_value * MOONSHOT_BUDGET_PCT, 2)
                budget       = min(ideal_budget, balance)
                log.info(f"💰 Alt budget: ${budget:.2f} "
                         f"(ideal ${ideal_budget:.2f} | free ${balance:.2f} | total ${total_value:.2f})")
                opp = find_moonshot_opportunity(tickers, budget,
                                                exclude=alt_excluded,
                                                open_symbols=open_symbols)
                if opp:
                    trade = open_position(opp, budget, MOONSHOT_TP, MOONSHOT_SL,
                                          "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                    if trade:
                        alt_trades.append(trade)
                        alt_excluded = set()
                else:
                    opp = find_reversal_opportunity(tickers, budget,
                                                    exclude=alt_excluded,
                                                    open_symbols=open_symbols)
                    if opp:
                        trade = open_position(opp, budget, REVERSAL_TP, REVERSAL_SL,
                                              "REVERSAL", max_hours=REVERSAL_MAX_HOURS)
                        if trade:
                            alt_trades.append(trade)
                            alt_excluded = set()

            # Monitor all open alt trades
            for trade in alt_trades[:]:
                should_exit, reason = check_exit(trade)
                if should_exit:
                    closed_label = trade["label"]
                    alt_excluded.add(trade["symbol"])
                    if close_position(trade, reason):
                        alt_trades.remove(trade)
                        log.info(f"🔄 [{closed_label}] Closed {trade['symbol']}. Re-scanning...")

            send_heartbeat(balance)
            send_daily_summary(balance)
            send_weekly_summary(balance)
            listen_for_commands(balance)
            time.sleep(5 if (scalper_trades or alt_trades) else SCAN_INTERVAL)

        except KeyboardInterrupt:
            log.info("🛑 Stopped.")
            for t in scalper_trades:
                log.warning(f"⚠️  Still holding {t['symbol']} (SCALPER) — close manually if live!")
            for t in alt_trades:
                log.warning(f"⚠️  Still holding {t['symbol']} ({t['label']}) — close manually if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway — it may need restarting.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nWill retry in 30s.")
            time.sleep(30)

run()
