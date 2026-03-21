"""
MEXC Trading Bot — 3 Strategies
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER  — Max 3 trades (30% each) | Trailing Stop | ATR SL | 1H trend aligned
  2. MOONSHOT — Max 2 trades (5%) | TP +25% | SL -7% | Bot-monitored exits only
  3. REVERSAL — Max 2 trades (5%) | TP +3%  | SL -2%  | Oversold bounce + volume capitulation
     Moonshot and Reversal share the alt slot.
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

MEXC_API_KEY    = "mx0vgls12Y6RKLCNcF"
MEXC_API_SECRET = "bb4627f25e3d4b86abe0b1eee2fe01bd"

PAPER_TRADE   = False
PAPER_BALANCE = 50.0

# ── Scalper (max 3 concurrent) ────────────────────────────────
SCALPER_MAX_TRADES  = 3
SCALPER_BUDGET_PCT  = 0.30
SCALPER_TP_LIMIT    = 0.10
SCALPER_TRAIL_ACT   = 0.02
SCALPER_TRAIL_PCT   = 0.01
SCALPER_ATR_MULT    = 1.5
SCALPER_SL          = 0.02
SCALPER_FLAT_MINS   = 30
SCALPER_FLAT_RANGE  = 0.005
SCALPER_ROTATE_GAP  = 20
SCALPER_MIN_VOL     = 500_000
SCALPER_MIN_PRICE   = 0.01
SCALPER_MIN_CHANGE  = 0.1
SCALPER_THRESHOLD   = 20
SCALPER_MAX_RSI     = 70

# ── Moonshot ──────────────────────────────────────────────────
# Max 2 concurrent — enough exposure without over-concentrating on thin markets
ALT_MAX_TRADES      = 2
MOONSHOT_BUDGET_PCT = 0.05
MOONSHOT_TP         = 0.25      # +25%
MOONSHOT_SL         = 0.07      # -7% (tightened from -10% — less bleed on failures)
MOONSHOT_MAX_VOL    = 500_000
MOONSHOT_MIN_VOL    = 5_000
MOONSHOT_MIN_1H     = 5.0       # min 5% move in last 1h
MOONSHOT_MIN_SCORE  = 20        # tightened from 15 — higher quality entries only
MOONSHOT_MAX_HOURS  = 1
MOONSHOT_MIN_DAYS   = 2
MOONSHOT_NEW_DAYS   = 14
MOONSHOT_MIN_VOL_BURST = 2.5    # min volume burst ratio (tightened from 2.0 for new, 3.0 for existing)

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
scalper_trades       = []
alt_trades           = []
last_heartbeat_at    = 0
last_daily_summary   = ""
last_weekly_summary  = ""
last_telegram_update = 0
last_top_scalper     = None
last_top_alt         = None

_symbol_rules         = {}
_symbol_rules_fetched = False
_symbol_rules_at      = 0
_api_blacklist        = set()
_scanner_log_buffer   = []
_MAX_SCANNER_LOGS     = 5
_paused               = False

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
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    _scanner_log_buffer.append(f"[{ts}] {msg}")
    while len(_scanner_log_buffer) > _MAX_SCANNER_LOGS:
        _scanner_log_buffer.pop(0)
    log.info(msg)

def public_get(path, params=None):
    r = requests.get(BASE_URL + path, params=params or {}, timeout=10)
    r.raise_for_status()
    return r.json()

def private_request(method, path, params=None):
    params = params or {}
    params["timestamp"] = int(time.time() * 1000)
    qs        = urllib.parse.urlencode(params)
    signature = hmac.new(MEXC_API_SECRET.encode("utf-8"), qs.encode("utf-8"), hashlib.sha256).hexdigest()
    url       = f"{BASE_URL}{path}?{qs}&signature={signature}"
    headers   = {"X-MEXC-APIKEY": MEXC_API_KEY}
    if   method == "GET":    r = requests.get(url,    headers=headers, timeout=10)
    elif method == "POST":   r = requests.post(url,   headers=headers, timeout=10)
    elif method == "DELETE": r = requests.delete(url, headers=headers, timeout=10)
    r.raise_for_status()
    return r.json()

def private_get(path, params=None):    return private_request("GET",    path, params)
def private_post(path, params=None):   return private_request("POST",   path, params)
def private_delete(path, params=None): return private_request("DELETE", path, params)

# ── Symbol rules ──────────────────────────────────────────────

def _load_symbol_rules():
    global _symbol_rules_fetched, _symbol_rules_at
    if _symbol_rules_fetched and (time.time() - _symbol_rules_at) < 86400:
        return
    log.info("📋 Loading symbol rules...")
    try:
        info = public_get("/api/v3/exchangeInfo")
        for s in info.get("symbols", []):
            sym = s["symbol"]
            min_qty = step_size = 1.0
            min_notional = 1.0
            tick_size = None
            for f in s.get("filters", []):
                if f["filterType"] == "LOT_SIZE":
                    min_qty   = float(f.get("minQty",   1.0))
                    step_size = float(f.get("stepSize", 1.0))
                if f["filterType"] == "MIN_NOTIONAL":
                    min_notional = float(f.get("minNotional", 1.0))
                if f["filterType"] == "PRICE_FILTER":
                    tick_size = f.get("tickSize")
            _symbol_rules[sym] = {
                "min_qty": min_qty, "step_size": step_size,
                "min_notional": min_notional, "tick_size": tick_size,
            }
        _symbol_rules_fetched = True
        _symbol_rules_at      = time.time()
        log.info(f"📋 Loaded rules for {len(_symbol_rules)} symbols.")
    except Exception as e:
        log.error(f"Symbol rules error: {e}")

def get_symbol_rules(symbol):
    r = _symbol_rules.get(symbol)
    if r:
        return r["min_qty"], r["step_size"], r["min_notional"], r.get("tick_size")
    return 1.0, 1.0, 1.0, None

def round_price_to_tick(price: float, tick_size) -> float:
    if not tick_size or float(tick_size) == 0:
        return round(price, 8)
    tick_str = tick_size.rstrip("0") or "1"
    decimals = len(tick_str.split(".")[1]) if "." in tick_str else 0
    return round(int(price / float(tick_size)) * float(tick_size), decimals)

def calc_qty(budget: float, price: float, step_size: float) -> float:
    raw      = budget / price
    floored  = math.floor(raw / step_size) * step_size
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
        return 0.0
    except Exception as e:
        log.error(f"Balance fetch failed: {e}")
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

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
    try:
        data = public_get("/api/v3/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        if not data:
            return None
        df = pd.DataFrame(data)
        df.columns = range(len(df.columns))
        df = df.rename(columns={0:"open_time", 1:"open", 2:"high", 3:"low", 4:"close", 5:"volume"})
        for col in ["open","high","low","close","volume"]:
            df[col] = pd.to_numeric(df[col], errors="coerce")
        df = df.dropna(subset=["close","volume"])
        return df if len(df) >= min_len else None
    except Exception as e:
        log.debug(f"Klines error {symbol}/{interval}: {e}")
        return None

def fetch_tickers() -> pd.DataFrame:
    data = public_get("/api/v3/ticker/24hr")
    df   = pd.DataFrame(data)
    df   = df[df["symbol"].str.endswith("USDT")].copy()
    for col in ["quoteVolume","volume","priceChangePercent","lastPrice"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    df["abs_change"] = df["priceChangePercent"].abs()
    return df.dropna(subset=["quoteVolume","lastPrice"])

def pick_tradeable(candidates: list, budget: float, label: str) -> dict | None:
    for c in candidates:
        min_qty, step_size, min_notional, _ = get_symbol_rules(c["symbol"])
        qty      = calc_qty(budget, c["price"], step_size)
        notional = round(qty * c["price"], 4)
        log.info(f"[{label}] {c['symbol']} qty={qty} notional=${notional:.2f} min=${min_notional:.2f}")
        if qty >= min_qty and notional >= min_notional:
            return c
    log.info(f"[{label}] All candidates failed notional/qty checks.")
    return None

# ── Scanner: Scalper ───────────────────────────────────────────

def evaluate_scalper_candidate(sym: str) -> dict | None:
    df_1h = parse_klines(sym, interval="60m", limit=60)
    if df_1h is None:
        return None
    if float(df_1h["close"].iloc[-1]) < calc_ema(df_1h["close"], 50).iloc[-1]:
        return None

    df5m = parse_klines(sym, interval="5m", limit=60)
    if df5m is None:
        return None

    close  = df5m["close"]
    volume = df5m["volume"]
    rsi    = calc_rsi(close)
    if np.isnan(rsi) or rsi > SCALPER_MAX_RSI:
        return None

    rsi_score = max(0, 40 - rsi) if rsi < 50 else 0
    ema9      = calc_ema(close, 9)
    ema21     = calc_ema(close, 21)
    crossed   = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
    ma_score  = 30 if crossed else (15 if ema9.iloc[-1] > ema21.iloc[-1] else 0)
    avg_vol   = volume.iloc[-20:-1].mean()
    vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
    vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
    score     = rsi_score + ma_score + vol_score

    if score < SCALPER_THRESHOLD:
        return None

    atr     = calc_atr(df5m)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    return {
        "symbol": sym, "score": round(score, 2), "rsi": round(rsi, 2),
        "vol_ratio": round(vol_ratio, 2), "price": float(close.iloc[-1]),
        "atr_pct": round(atr_pct, 6),
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

    log.info(f"🔍 [SCALPER] {len(candidates)} candidates after ticker filters")

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

    log.info(f"🔍 [SCALPER] Scoring {len(established)} pairs (parallel)...")
    scores = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(evaluate_scalper_candidate, sym): sym for sym in established}
        for f in as_completed(futures):
            result = f.result()
            if result:
                scores.append(result)

    if not scores:
        scanner_log("🔍 [SCALPER] No qualifying pairs.")
        return None

    scores.sort(key=lambda x: x["score"], reverse=True)
    best = scores[0]
    last_top_scalper = best

    vol_row  = tickers[tickers["symbol"] == best["symbol"]]
    best_vol = float(vol_row["quoteVolume"].iloc[0]) if not vol_row.empty else 0
    scanner_log(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
                f"vol: ${best_vol:,.0f} | RSI: {best['rsi']} | ATR: {best['atr_pct']*100:.2f}%")

    return pick_tradeable(scores, budget, "SCALPER")

# ── Scanner: Moonshot ──────────────────────────────────────────

def get_1h_change(symbol: str) -> float | None:
    try:
        # ⚠️ MEXC requires "60m" not "1h"
        df = parse_klines(symbol, interval="60m", limit=3, min_len=2)
        if df is None:
            return None
        prev = float(df["close"].iloc[-2])
        curr = float(df["close"].iloc[-1])
        return (curr - prev) / prev * 100 if prev > 0 else None
    except:
        return None


def find_new_listings(tickers: pd.DataFrame, exclude: set, open_symbols: set) -> list:
    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(60)["symbol"].tolist()

    new = []
    for sym in candidates:
        try:
            data     = public_get("/api/v3/klines", {"symbol": sym, "interval": "1d", "limit": MOONSHOT_NEW_DAYS})
            days_old = len(data) if data else 0
            if MOONSHOT_MIN_DAYS <= days_old < MOONSHOT_NEW_DAYS:
                new.append({"symbol": sym, "days_old": days_old})
        except:
            pass
        time.sleep(0.05)

    log.info(f"🌙 [MOONSHOT] {len(new)} new listings ({MOONSHOT_MIN_DAYS}-{MOONSHOT_NEW_DAYS} days)")
    return new


def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float,
                               exclude: set, open_symbols: set) -> dict | None:
    global last_top_alt

    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"] <= MOONSHOT_MAX_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    momentum_candidates = df.sort_values("priceChangePercent", ascending=False).head(40)["symbol"].tolist()

    new_listings = find_new_listings(tickers, exclude=exclude, open_symbols=open_symbols)
    new_symbols  = [n["symbol"] for n in new_listings]
    all_candidates = list(dict.fromkeys(new_symbols + momentum_candidates))

    log.info(f"🌙 [MOONSHOT] {len(all_candidates)} candidates ({len(new_symbols)} new + {len(momentum_candidates)} momentum)")
    if not all_candidates:
        return None

    scores = []
    for sym in all_candidates:
        change_1h = get_1h_change(sym)
        is_new    = sym in new_symbols

        if is_new:
            if change_1h is not None and change_1h < 0:
                time.sleep(0.1); continue
        else:
            if change_1h is None or change_1h < MOONSHOT_MIN_1H:
                time.sleep(0.1); continue

        # ⚠️ MEXC requires "60m" not "1h"
        interval = "60m" if is_new else "15m"
        df_k     = parse_klines(sym, interval=interval, limit=60)
        if df_k is None:
            time.sleep(0.1); continue

        close     = df_k["close"]
        volume    = df_k["volume"]
        rsi       = calc_rsi(close)
        if np.isnan(rsi):
            time.sleep(0.1); continue

        rsi_score = max(0, 40 - rsi) if rsi < 50 else 0
        ema9      = calc_ema(close, 9); ema21 = calc_ema(close, 21)
        crossed   = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        ma_score  = 30 if crossed else (15 if ema9.iloc[-1] > ema21.iloc[-1] else 0)
        avg_vol   = volume.iloc[-20:-1].mean()
        vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
        score     = rsi_score + ma_score + vol_score

        if score >= MOONSHOT_MIN_SCORE:
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

    # Burst detection — tightened: single threshold of MOONSHOT_MIN_VOL_BURST for both types
    tradeable = []
    for s in scores:
        df_k   = s.pop("_df", None)
        is_new = s.pop("_is_new", False)
        s.pop("_1h_chg", None)

        if df_k is None or len(df_k) < 6:
            tradeable.append(s); continue

        close  = df_k["close"]; volume = df_k["volume"]; opens = df_k["open"]
        avg_vol     = volume.iloc[-11:-1].mean()
        vol_burst   = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        candle_moves= (close - opens).abs() / opens * 100
        avg_move    = candle_moves.iloc[-11:-1].mean()
        price_burst = (float(candle_moves.iloc[-1]) / avg_move) if avg_move > 0 else 1.0
        greens      = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])

        # Require either strong volume OR strong price burst (not both required)
        if vol_burst < MOONSHOT_MIN_VOL_BURST and price_burst < 2.0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — burst too weak (vol:{vol_burst:.1f}x price:{price_burst:.1f}x)")
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
    df5m = parse_klines(sym, interval="5m", limit=60, min_len=30)
    if df5m is None:
        return None

    if float(df5m["close"].iloc[-1]) <= float(df5m["open"].iloc[-1]):
        return None

    volume   = df5m["volume"]
    avg_vol  = float(volume.iloc[-20:-2].mean())
    prev_vol = float(volume.iloc[-2])
    if avg_vol > 0 and prev_vol < avg_vol * 1.5:
        return None

    rsi = calc_rsi(df5m["close"])
    if np.isnan(rsi) or rsi > REVERSAL_MAX_RSI:
        return None

    return {
        "symbol": sym, "price": float(df5m["close"].iloc[-1]),
        "rsi": round(rsi, 2), "score": round(rsi, 2),
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

    log.info(f"🔄 [REVERSAL] {len(candidates)} candidates")
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
        scanner_log("🔄 [REVERSAL] No oversold pairs with capitulation + green candle.")
        return None

    tradeable.sort(key=lambda x: x["rsi"])
    best = tradeable[0]
    last_top_alt = best
    scanner_log(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | ${best['price']:.6f}")

    return pick_tradeable(tradeable, budget, "REVERSAL")

# ── Order execution ────────────────────────────────────────────

def place_market_buy(symbol, qty, label=""):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] BUY {qty} {symbol}")
        return {"orderId": f"PAPER_BUY_{int(time.time())}"}
    try:
        result = private_post("/api/v3/order", {
            "symbol": symbol, "side": "BUY", "type": "MARKET", "quantity": str(qty)
        })
        log.info(f"✅ [{label}] BUY placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:    body = e.response.json()
        except: body = e.response.text if e.response else "no response"
        if isinstance(body, dict) and body.get("code") == 10007:
            _api_blacklist.add(symbol)
            log.warning(f"⚠️ [{label}] {symbol} not API-tradeable — blacklisted.")
        else:
            log.error(f"🚨 [{label}] BUY rejected: {body}")
            telegram(f"🚨 <b>BUY rejected</b> [{label}]\n{symbol} qty={qty}\n{str(body)[:300]}")
        return None


def place_limit_sell(symbol, qty, price, label="", tag=""):
    if PAPER_TRADE:
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
        try:    body = e.response.json()
        except: body = e.response.text if e.response else "no response"
        log.error(f"🚨 [{label}] LIMIT SELL rejected: {body}")
        return None


def cancel_order(symbol, order_id, label=""):
    if PAPER_TRADE:
        return
    try:
        private_delete("/api/v3/order", {"symbol": symbol, "orderId": order_id})
        log.info(f"✅ [{label}] Cancelled {order_id}")
    except Exception as e:
        log.debug(f"[{label}] Cancel failed (may be filled): {e}")


def get_open_order_ids(symbol) -> set:
    if PAPER_TRADE:
        return set()
    try:
        orders = private_get("/api/v3/openOrders", {"symbol": symbol})
        return {o["orderId"] for o in orders}
    except Exception as e:
        log.debug(f"get_open_order_ids {symbol}: {e}")
        return set()

# ── Trade lifecycle ────────────────────────────────────────────

def open_position(opp, budget_usdt, tp_pct, sl_pct, label,
                  max_hours=None, sl_override_pct=None):
    symbol                              = opp["symbol"]
    min_qty, step_size, min_notional, tick_size = get_symbol_rules(symbol)

    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.warning(f"[{label}] Fresh price failed: {e}")
        price = opp["price"]

    qty      = calc_qty(budget_usdt, price, step_size)
    notional = round(qty * price, 4)

    if qty < min_qty:
        log.warning(f"[{label}] {symbol} qty {qty} < min {min_qty}")
        return None
    if notional < min_notional:
        log.warning(f"[{label}] {symbol} notional ${notional:.2f} < min ${min_notional:.2f}")
        return None

    if not place_market_buy(symbol, qty, label):
        return None

    actual_sl = sl_override_pct if sl_override_pct else sl_pct
    tp_price  = round_price_to_tick(price * (1 + tp_pct), tick_size)
    sl_price  = round(price * (1 - actual_sl), 8)

    # ── KEY FIX: SCALPER gets exchange TP limit order ─────────
    # MOONSHOT/REVERSAL: NO limit order — bot-monitored only.
    # This eliminates the cancel+market sell race condition on thin markets
    # that was causing positions to stay open and bleed losses.
    if label == "SCALPER":
        tp_order_id = place_limit_sell(symbol, qty, tp_price, label, tag="TP")
        if not PAPER_TRADE and not tp_order_id:
            log.warning(f"[{label}] TP limit failed — monitoring manually.")
            telegram(f"⚠️ [{label}] TP limit failed for {symbol} — monitoring manually.")
        tp_status = "TP ✅ on exchange" if tp_order_id else "TP monitored by bot"
    else:
        tp_order_id = None
        tp_status   = "TP + SL bot-monitored ✅ (direct market sell)"

    trade = {
        "label":         label,
        "symbol":        symbol,
        "entry_price":   price,
        "qty":           qty,
        "budget_used":   notional,
        "tp_price":      tp_price,
        "sl_price":      sl_price,
        "tp_pct":        tp_pct,
        "sl_pct":        actual_sl,
        "tp_order_id":   tp_order_id,
        "highest_price": price,
        "max_hours":     max_hours,
        "opened_at":     datetime.now(timezone.utc).isoformat(),
        "score":         opp.get("score", 0),
        "rsi":           opp.get("rsi", 0),
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icon         = {"SCALPER":"🟢","MOONSHOT":"🌙","REVERSAL":"🔄"}.get(label,"🟢")
    timeout_line = f"Max hold:    {max_hours}h\n" if max_hours else ""

    log.info(f"{icon} [{label}] Opened {symbol} | ${notional:.2f} | "
             f"Entry: {price:.6f} | TP: {tp_price:.6f} | SL: {sl_price:.6f} (-{actual_sl*100:.1f}%)")
    telegram(
        f"{icon} <b>Trade Opened — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${notional:.2f} USDT</b>\n"
        f"Entry:       <b>${price:.6f}</b>\n"
        f"Take profit: <b>${tp_price:.6f}</b>  (+{tp_pct*100:.0f}%)\n"
        f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl*100:.1f}%) [market]\n"
        f"{timeout_line}"
        f"{tp_status}\n"
        f"Score: {opp.get('score',0)} | RSI: {opp.get('rsi','?')} | Vol: {opp.get('vol_ratio','?')}x"
    )
    return trade


def check_exit(trade, best_score: float = 0) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")

    # Timeout
    if trade.get("max_hours"):
        held_h = (datetime.now(timezone.utc) -
                  datetime.fromisoformat(trade["opened_at"])).total_seconds() / 3600
        if held_h >= trade["max_hours"]:
            log.info(f"⏰ [{label}] Timeout: {symbol}")
            if not PAPER_TRADE and tp_order_id:
                cancel_order(symbol, tp_order_id, label)
            return True, "TIMEOUT"

    try:
        price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception as e:
        log.error(f"Price fetch error {symbol}: {e}")
        return False, ""

    pct      = (price - trade["entry_price"]) / trade["entry_price"] * 100
    held_min = (datetime.now(timezone.utc) -
                datetime.fromisoformat(trade["opened_at"])).total_seconds() / 60
    trade["highest_price"] = max(trade.get("highest_price", price), price)

    # Hard safety SL -5%
    if pct <= -5.0:
        log.info(f"🚨 [{label}] Hard SL: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # Normal SL
    if price <= trade["sl_price"]:
        log.info(f"🛑 [{label}] SL: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # ── TP exit logic ─────────────────────────────────────────
    # SCALPER: check if exchange limit order was filled
    # MOONSHOT/REVERSAL: pure price polling — no cancel step needed, no race condition
    if label == "SCALPER":
        if not PAPER_TRADE and tp_order_id:
            if tp_order_id not in get_open_order_ids(symbol):
                log.info(f"🎯 [{label}] TP limit filled: {symbol}")
                return True, "TAKE_PROFIT"
        if PAPER_TRADE or not tp_order_id:
            if price >= trade["tp_price"]:
                log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
                return True, "TAKE_PROFIT"
    else:
        # MOONSHOT/REVERSAL: simple price check, clean market sell follows
        if price >= trade["tp_price"]:
            log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
            return True, "TAKE_PROFIT"

    # SCALPER-specific exits
    if label == "SCALPER":
        if trade["highest_price"] >= trade["entry_price"] * (1 + SCALPER_TRAIL_ACT):
            if price <= trade["highest_price"] * (1 - SCALPER_TRAIL_PCT):
                log.info(f"📉 [{label}] Trailing stop: {symbol} | {pct:+.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TRAILING_STOP"

        if held_min >= SCALPER_FLAT_MINS and abs(pct) <= SCALPER_FLAT_RANGE * 100:
            log.info(f"😴 [{label}] Flat exit: {symbol} | {pct:+.2f}%")
            if not PAPER_TRADE and tp_order_id:
                cancel_order(symbol, tp_order_id, label)
            return True, "FLAT_EXIT"

        if best_score > 0 and pct < SCALPER_TRAIL_ACT * 100:
            if (best_score - trade.get("score", 0)) >= SCALPER_ROTATE_GAP:
                log.info(f"🔀 [{label}] Rotation: {symbol} | {pct:+.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "ROTATION"

    log.info(f"👀 [{label}] {symbol} | {pct:+.2f}% | {held_min:.0f}min | "
             f"High: {((trade['highest_price']/trade['entry_price'])-1)*100:.2f}%")
    return False, ""


def close_position(trade, reason) -> bool:
    label  = trade["label"]
    symbol = trade["symbol"]

    # For MOONSHOT/REVERSAL: market sell on ALL exits including TAKE_PROFIT
    # (no exchange limit order was placed, so we always need to sell manually)
    # For SCALPER: TAKE_PROFIT is handled by exchange limit, others need market sell
    needs_sell = (
        (label in ("MOONSHOT", "REVERSAL")) or
        (label == "SCALPER" and reason in ("STOP_LOSS","TRAILING_STOP","TIMEOUT","FLAT_EXIT","ROTATION"))
    )

    if needs_sell and not PAPER_TRADE:
        try:
            result = private_post("/api/v3/order", {
                "symbol": symbol, "side": "SELL",
                "type": "MARKET", "quantity": str(trade["qty"])
            })
            log.info(f"✅ [{label}] Market sell ({reason}): {result}")
        except requests.exceptions.HTTPError as e:
            try:    body = e.response.json()
            except: body = e.response.text if e.response else "no response"
            log.error(f"🚨 [{label}] Market sell failed: {body}")
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
    win_rate  = len(wins) / len(trade_history) * 100 if trade_history else 0
    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons     = {
        "TAKE_PROFIT":   ("🎯","Take Profit Hit"),
        "STOP_LOSS":     ("🛑","Stop Loss Hit"),
        "TRAILING_STOP": ("📉","Trailing Stop Hit"),
        "FLAT_EXIT":     ("😴","Flat Exit"),
        "ROTATION":      ("🔀","Rotated"),
        "TIMEOUT":       ("⏰","Timeout Exit"),
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
        f"Session: {len(trade_history)} trades | Win: {win_rate:.0f}% | P&L: ${total_pnl:+.2f}"
    )
    log.info(f"📈 Closed {symbol} [{reason}] {pnl_pct:+.2f}% | Win:{win_rate:.0f}% P&L:${total_pnl:+.2f}")
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

    scalper_lines = []
    for t in scalper_trades:
        try:
            px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            scalper_lines.append(f"  🟢 {t['symbol']} {pct:+.2f}%")
        except:
            scalper_lines.append(f"  🟢 {t['symbol']}")
    if not scalper_trades:
        if last_top_scalper:
            scalper_lines.append(f"  Watching: {last_top_scalper['symbol']} (score {last_top_scalper['score']})")
        else:
            scalper_lines.append("  Scanning...")

    alt_lines = []
    for t in alt_trades:
        try:
            px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            alt_lines.append(f"  {t['label']}: <b>{t['symbol']}</b> {pct:+.2f}%")
        except:
            alt_lines.append(f"  {t['label']}: <b>{t['symbol']}</b>")
    if not alt_trades:
        if last_top_alt:
            alt_lines.append(f"  Watching: {last_top_alt['symbol']} (score {last_top_alt['score']})")
        else:
            alt_lines.append("  Scanning...")

    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance:  <b>${balance:.2f} USDT</b>\n"
        f"Scalpers ({len(scalper_trades)}/{SCALPER_MAX_TRADES}):\n"
        + "\n".join(scalper_lines) + "\n"
        + f"Alt ({len(alt_trades)}/{ALT_MAX_TRADES}):\n"
        + "\n".join(alt_lines) + "\n"
        + f"Trades today: {trades_today}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"<i>/status · /pnl · /logs · /config · /pause · /resume · /close</i>"
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
            ts = [t for t in trade_history if t.get("label") == lbl]
            if not ts: return ""
            wins = [t for t in ts if t["pnl_pct"] > 0]
            return (f"\n<b>{lbl}</b>: {len(ts)} trades | "
                    f"Win: {len(wins)/len(ts)*100:.0f}% | "
                    f"P&L: ${sum(t['pnl_usdt'] for t in ts):+.2f}")
        total = sum(t["pnl_usdt"] for t in trade_history)
        telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━"
                 + block("SCALPER") + block("MOONSHOT") + block("REVERSAL")
                 + f"\n━━━━━━━━━━━━━━━\nTotal P&L: <b>${total:+.2f}</b>\nBalance: <b>${balance:.2f}</b>")
        return

    try:
        now_ms  = int(time.time() * 1000)
        symbols = list({t["symbol"] for t in trade_history})
        if not symbols:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return
        all_fills = []
        for sym in symbols:
            try:
                fills = private_get("/api/v3/myTrades", {"symbol": sym, "startTime": now_ms - 86400_000, "limit": 1000})
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
        buys  = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells = {o: v for o, v in orders.items() if v["side"] == "SELL"}
        bought = sum(v["cost"] for v in buys.values())
        sold   = sum(v["cost"] for v in sells.values())
        net    = round(sold - bought, 4)
        emoji  = "📈" if net >= 0 else "📉"
        syms   = ", ".join(sorted({v["symbol"] for v in orders.values()})[:5])
        telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
                 f"Orders: <b>{len(buys)} buys / {len(sells)} sells</b>\n"
                 f"Pairs:  <b>{syms}</b>\n"
                 f"Bought: <b>${bought:,.2f}</b>  Sold: <b>${sold:,.2f}</b>\n"
                 f"Net P&L: {emoji} <b>${net:+.2f}</b>\nBalance: <b>${balance:.2f}</b>")
    except Exception as e:
        log.error(f"Daily summary failed: {e}")

# ── Weekly P&L ────────────────────────────────────────────────

def fetch_mexc_weekly_pnl() -> dict:
    if PAPER_TRADE:
        cut = datetime.now(timezone.utc).timestamp() - 7 * 86400
        wt  = [t for t in trade_history
               if datetime.fromisoformat(t.get("closed_at","1970-01-01")).timestamp() >= cut]
        wins = [t for t in wt if t["pnl_pct"] > 0]
        losses = [t for t in wt if t["pnl_pct"] <= 0]
        return {
            "total": len(wt), "wins": len(wins), "losses": len(losses),
            "pnl_usdt": round(sum(t["pnl_usdt"] for t in wt), 4),
            "best":  max(wt, key=lambda t: t["pnl_pct"]) if wt else None,
            "worst": min(wt, key=lambda t: t["pnl_pct"]) if wt else None,
        }
    try:
        now_ms  = int(time.time() * 1000)
        symbols = list({t["symbol"] for t in trade_history})
        if not symbols:
            return {"total":0,"buys":0,"sells":0,"pnl_usdt":0.0,"total_bought":0.0,"total_sold":0.0}
        all_fills = []
        for sym in symbols:
            try:
                fills = private_get("/api/v3/myTrades", {"symbol": sym, "startTime": now_ms - 7*86400_000, "limit": 1000})
                if fills: all_fills.extend(fills)
            except: pass
            time.sleep(0.1)
        if not all_fills:
            return {"error": "No fills found"}
        orders = defaultdict(lambda: {"symbol":"","qty":0,"cost":0,"side":""})
        for fill in all_fills:
            oid = fill["orderId"]
            orders[oid]["symbol"] = fill["symbol"]
            orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
            orders[oid]["qty"]   += float(fill["qty"])
            orders[oid]["cost"]  += float(fill["quoteQty"])
        buys    = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells   = {o: v for o, v in orders.items() if v["side"] == "SELL"}
        bought  = sum(v["cost"] for v in buys.values())
        sold    = sum(v["cost"] for v in sells.values())
        bsyms   = Counter(v["symbol"] for v in buys.values())
        ssyms   = Counter(v["symbol"] for v in sells.values())
        done    = sum(min(bsyms[s], ssyms[s]) for s in bsyms)
        return {"total":done,"buys":len(buys),"sells":len(sells),
                "pnl_usdt":round(sold-bought,4),
                "total_bought":round(bought,2),"total_sold":round(sold,2)}
    except Exception as e:
        return {"error": str(e)}


def build_weekly_message(pnl: dict, balance: float) -> str:
    mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    emoji = "📈" if pnl.get("pnl_usdt",0) >= 0 else "📉"
    if "error" in pnl:
        return f"📊 <b>Weekly P&L</b> [{mode}]\n━━━━━━━━━━━━━━━\nError: {pnl['error']}"
    if PAPER_TRADE:
        wr  = f"{pnl['wins']/pnl['total']*100:.0f}%" if pnl.get("total") else "n/a"
        msg = (f"{emoji} <b>Weekly Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
               f"Trades:   <b>{pnl['total']}</b>  ({pnl.get('wins',0)}W/{pnl.get('losses',0)}L)\n"
               f"Win rate: <b>{wr}</b>\nP&L: <b>${pnl['pnl_usdt']:+.2f}</b>\n"
               f"Balance:  <b>${balance:.2f}</b>")
        if pnl.get("best"):  msg += f"\nBest:  {pnl['best']['symbol']} {pnl['best']['pnl_pct']:+.2f}%"
        if pnl.get("worst"): msg += f"\nWorst: {pnl['worst']['symbol']} {pnl['worst']['pnl_pct']:+.2f}%"
        return msg
    return (f"{emoji} <b>Weekly Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
            f"Round trips:  <b>{pnl['total']}</b>\n"
            f"Total bought: <b>${pnl['total_bought']:,.2f}</b>\n"
            f"Total sold:   <b>${pnl['total_sold']:,.2f}</b>\n"
            f"Net P&L:      <b>${pnl['pnl_usdt']:+.2f}</b>\n"
            f"Balance:      <b>${balance:.2f}</b>")


def send_weekly_summary(balance: float):
    global last_weekly_summary
    now  = datetime.now(timezone.utc)
    week = f"{now.isocalendar()[0]}-W{now.isocalendar()[1]:02d}"
    if last_weekly_summary == week or now.weekday() != 0 or now.hour != 0:
        return
    last_weekly_summary = week
    telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))

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
            if str(msg.get("chat",{}).get("id")) != str(TELEGRAM_CHAT_ID):
                continue

            if text in ("/pnl",):
                telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))

            elif text in ("/status",):
                mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
                lines = [f"📋 <b>Status</b> [{mode}]\n━━━━━━━━━━━━━━━"]
                for t in scalper_trades:
                    try:
                        px  = float(public_get("/api/v3/ticker/price",{"symbol":t["symbol"]})["price"])
                        pct = (px - t["entry_price"]) / t["entry_price"] * 100
                        lines.append(f"🟢 {t['symbol']} | {pct:+.2f}% | "
                                     f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
                    except:
                        lines.append(f"🟢 {t['symbol']} (unavailable)")
                if not scalper_trades:
                    lines.append("Scalper: scanning...")
                for t in alt_trades:
                    try:
                        px  = float(public_get("/api/v3/ticker/price",{"symbol":t["symbol"]})["price"])
                        pct = (px - t["entry_price"]) / t["entry_price"] * 100
                        lines.append(f"{t['label']}: <b>{t['symbol']}</b> | {pct:+.2f}% | "
                                     f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
                    except:
                        lines.append(f"{t['label']}: {t['symbol']} (unavailable)")
                if not alt_trades:
                    lines.append("Alt: scanning...")
                lines.append(f"Balance: <b>${balance:.2f} USDT</b>")
                telegram("\n".join(lines))

            elif text in ("/logs",):
                if _scanner_log_buffer:
                    out = "📜 <b>Last Scanner Activity</b>\n━━━━━━━━━━━━━━━\n"
                    out += "\n".join(f"<code>{l}</code>" for l in _scanner_log_buffer)
                else:
                    out = "📜 No scanner activity yet."
                telegram(out)

            elif text in ("/pause",):
                _paused = True
                telegram("⏸️ <b>Paused.</b> No new trades. Existing positions monitored.\n/resume to restart.")

            elif text in ("/resume",):
                _paused = False
                telegram("▶️ <b>Resumed.</b> Scanning for new trades.")

            elif text in ("/close",):
                telegram("🚨 <b>Emergency close triggered.</b>")
                closed = 0
                for t in scalper_trades[:]:
                    if close_position(t, "STOP_LOSS"):
                        scalper_trades.remove(t); closed += 1
                for t in alt_trades[:]:
                    if close_position(t, "STOP_LOSS"):
                        alt_trades.remove(t); closed += 1
                telegram(f"✅ Closed {closed} position(s).")

            elif text in ("/config",):
                telegram(
                    f"⚙️ <b>Current Config</b>\n━━━━━━━━━━━━━━━\n"
                    f"🟢 <b>Scalper</b>\n"
                    f"  Max: {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}% | "
                    f"TP +{SCALPER_TP_LIMIT*100:.0f}% | ATR ×{SCALPER_ATR_MULT}\n"
                    f"  Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.0f}%\n"
                    f"\n🌙 <b>Moonshot</b>  [bot-monitored]\n"
                    f"  Max: {ALT_MAX_TRADES} trades\n"
                    f"  TP: +{MOONSHOT_TP*100:.0f}%  SL: -{MOONSHOT_SL*100:.0f}%  Max: {MOONSHOT_MAX_HOURS}h\n"
                    f"  Min score: {MOONSHOT_MIN_SCORE} | Min vol burst: {MOONSHOT_MIN_VOL_BURST}x\n"
                    f"\n🔄 <b>Reversal</b>  [bot-monitored]\n"
                    f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  Max: {REVERSAL_MAX_HOURS}h\n"
                    f"\n{'⏸️ PAUSED' if _paused else '▶️ RUNNING'}"
                )

    except Exception as e:
        log.debug(f"Telegram poll error: {e}")

# ── Startup reconciliation ─────────────────────────────────────

def reconcile_open_positions():
    if PAPER_TRADE:
        return
    try:
        open_orders = private_get("/api/v3/openOrders", {})
        if not open_orders:
            return
        symbols = list({o["symbol"] for o in open_orders})
        log.warning(f"⚠️  Found {len(open_orders)} open orders at startup: {symbols}")
        telegram(
            f"⚠️ <b>Bot restarted with open orders!</b>\n━━━━━━━━━━━━━━━\n"
            f"Found {len(open_orders)} open order(s): <b>{', '.join(symbols)}</b>\n\n"
            f"SL is no longer active for these positions.\n"
            f"👉 Please check MEXC and close any losing positions manually."
        )
    except Exception as e:
        log.error(f"Reconcile failed: {e}")

# ── Main loop ──────────────────────────────────────────────────

def run():
    global scalper_trades, alt_trades

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")

    _load_symbol_rules()
    reconcile_open_positions()

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (max {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%)\n"
        f"  TP: +{SCALPER_TP_LIMIT*100:.0f}% limit | ATR ×{SCALPER_ATR_MULT} SL\n"
        f"\n🌙 <b>Moonshot</b> (max {ALT_MAX_TRADES} trades, 5% each) [bot-monitored]\n"
        f"  TP: +{MOONSHOT_TP*100:.0f}%  SL: -{MOONSHOT_SL*100:.0f}%  max {MOONSHOT_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b> (5%) [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  max {REVERSAL_MAX_HOURS}h\n"
        f"\n<i>/status · /pnl · /logs · /config · /pause · /resume · /close</i>"
    )

    scalper_excluded = set()
    alt_excluded     = set()

    while True:
        try:
            balance = get_available_balance()
            _load_symbol_rules()

            open_symbols = {t["symbol"] for t in scalper_trades + alt_trades}

            total_value = balance
            for t in scalper_trades + alt_trades:
                if not PAPER_TRADE:
                    try:
                        px = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
                        total_value += px * t["qty"]
                    except:
                        total_value += t["budget_used"]
                else:
                    total_value += t["budget_used"]

            need_scan = ((not _paused and len(scalper_trades) < SCALPER_MAX_TRADES)
                         or len(alt_trades) < ALT_MAX_TRADES)
            tickers   = fetch_tickers() if need_scan else None

            # ── Scalper ───────────────────────────────────────
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
                        scalper_excluded = set()
            else:
                rot_t      = tickers if tickers is not None else fetch_tickers()
                budget     = round(balance * SCALPER_BUDGET_PCT, 2)
                best_opp   = find_scalper_opportunity(rot_t, budget,
                                                      exclude=scalper_excluded,
                                                      open_symbols=open_symbols)
                best_score = best_opp["score"] if best_opp else 0

                for trade in scalper_trades[:]:
                    tpct     = (trade.get("highest_price", trade["entry_price"]) /
                                trade["entry_price"] - 1) * 100
                    worst    = min((t.get("highest_price", t["entry_price"]) /
                                   t["entry_price"] - 1) * 100 for t in scalper_trades)
                    is_worst = abs(tpct - worst) < 0.01
                    s_arg    = best_score if is_worst else 0

                    should_exit, reason = check_exit(trade, best_score=s_arg)
                    if should_exit:
                        scalper_excluded.add(trade["symbol"])
                        if close_position(trade, reason):
                            scalper_trades.remove(trade)
                            if reason == "ROTATION" and best_opp:
                                sl_atr = best_opp["atr_pct"] * SCALPER_ATR_MULT
                                new_t  = open_position(best_opp, budget, SCALPER_TP_LIMIT,
                                                       SCALPER_SL, "SCALPER",
                                                       sl_override_pct=sl_atr)
                                if new_t:
                                    scalper_trades.append(new_t)
                                    scalper_excluded = set()

            # ── Alt (Moonshot / Reversal) ─────────────────────
            if not _paused and len(alt_trades) < ALT_MAX_TRADES:
                ideal  = round(total_value * MOONSHOT_BUDGET_PCT, 2)
                budget = min(ideal, balance)
                log.info(f"💰 Alt budget: ${budget:.2f} "
                         f"(ideal ${ideal:.2f} | free ${balance:.2f} | total ${total_value:.2f})")

                opp = find_moonshot_opportunity(tickers, budget,
                                                exclude=alt_excluded,
                                                open_symbols=open_symbols)
                if opp:
                    trade = open_position(opp, budget, MOONSHOT_TP, MOONSHOT_SL,
                                          "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                    if trade:
                        alt_trades.append(trade); alt_excluded = set()
                else:
                    opp = find_reversal_opportunity(tickers, budget,
                                                    exclude=alt_excluded,
                                                    open_symbols=open_symbols)
                    if opp:
                        trade = open_position(opp, budget, REVERSAL_TP, REVERSAL_SL,
                                              "REVERSAL", max_hours=REVERSAL_MAX_HOURS)
                        if trade:
                            alt_trades.append(trade); alt_excluded = set()

            for trade in alt_trades[:]:
                should_exit, reason = check_exit(trade)
                if should_exit:
                    alt_excluded.add(trade["symbol"])
                    if close_position(trade, reason):
                        alt_trades.remove(trade)

            send_heartbeat(balance)
            send_daily_summary(balance)
            send_weekly_summary(balance)
            listen_for_commands(balance)
            time.sleep(5 if (scalper_trades or alt_trades) else SCAN_INTERVAL)

        except KeyboardInterrupt:
            log.info("🛑 Stopped.")
            for t in scalper_trades + alt_trades:
                log.warning(f"⚠️  Holding {t['symbol']} ({t['label']}) — close manually if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nRetrying in 30s.")
            time.sleep(30)

run()
