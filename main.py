"""
MEXC Trading Bot — 3 Strategies
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER  — Max 3 trades (30% each) | ATR TP (2:1 R:R) | ATR SL | 1H trend | 30min watchlist
  2. MOONSHOT — Max 2 trades (5%) | TP +15% | SL -5% | Bot-monitored exits only
  3. REVERSAL — Max 2 trades (5%) | TP +4%  | SL -2% | Oversold bounce + volume capitulation
     Moonshot and Reversal share the alt slot.
"""

import time, hmac, hashlib, logging, requests, math, json, os
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
SCALPER_MAX_TRADES   = 3
SCALPER_BUDGET_PCT   = 0.30
SCALPER_TP_ATR_MULT  = 3.0       # TP = 3×ATR (vs SL = 1.5×ATR → guaranteed 2:1 R:R)
SCALPER_TP_LIMIT     = 0.10      # fallback TP if ATR unavailable (+10%)
SCALPER_TRAIL_ACT    = 0.03      # trailing stop activates at +3%
SCALPER_TRAIL_PCT    = 0.015     # trail 1.5% below highest price
SCALPER_ATR_MULT     = 1.5       # SL = 1.5×ATR
SCALPER_ATR_PERIOD   = 21        # ATR period — 21 candles smoother than 14, less SL hunting
SCALPER_SL           = 0.02      # fallback SL if ATR unavailable (2%)
SCALPER_FLAT_MINS    = 30
SCALPER_FLAT_RANGE   = 0.005
SCALPER_ROTATE_GAP   = 20
SCALPER_MIN_VOL      = 500_000
SCALPER_MIN_PRICE    = 0.01
SCALPER_MIN_CHANGE   = 0.1
SCALPER_THRESHOLD    = 40        # raised from 20 — only take high-quality entries
SCALPER_MAX_RSI      = 70
# Breakeven trail — high-confidence trades (score ≥ this) move SL to entry at +1.5%
# Locks in a no-loss position before the normal trailing stop activates at +3%
SCALPER_BREAKEVEN_SCORE = 60     # score threshold for fast breakeven
SCALPER_BREAKEVEN_ACT   = 0.015  # move SL to entry once trade is up this much (+1.5%)
SCALPER_MIN_1H_VOL      = 50_000 # min $50k USDT volume in last 12×5m candles (~1h)
                                  # thin pairs gap hard through SL on market sells
SCALPER_SYMBOL_COOLDOWN = 1800   # seconds before re-entering a symbol after SL (30 min)
SCALPER_DAILY_LOSS_PCT  = 0.05   # stop new scalper entries if session down >5% of starting balance

# ── Watchlist — universe of pairs pre-scored every 30 minutes ──
WATCHLIST_SIZE      = 30        # top N pairs by score to trade from
WATCHLIST_TTL       = 1800      # seconds between full rescores (30 min)

# ── Moonshot ──────────────────────────────────────────────────
ALT_MAX_TRADES      = 2
MOONSHOT_BUDGET_PCT = 0.05
MOONSHOT_TP         = 0.15      # +15% (was +25% — more achievable in 1h)
MOONSHOT_SL         = 0.05      # -5% (tightened from -7% — 1h window, cut fast)
MOONSHOT_MAX_VOL    = 500_000
MOONSHOT_MIN_VOL    = 5_000
MOONSHOT_MIN_1H     = 5.0
MOONSHOT_MIN_SCORE  = 20
MOONSHOT_MAX_HOURS  = 1
MOONSHOT_MIN_DAYS   = 2
MOONSHOT_NEW_DAYS   = 14
MOONSHOT_MIN_VOL_BURST = 2.5

# ── Reversal ──────────────────────────────────────────────────
REVERSAL_TP         = 0.040     # +4% (was +3% — better R:R at 2:1)
REVERSAL_SL         = 0.020     # -2% unchanged
REVERSAL_MIN_VOL    = 100_000
REVERSAL_MAX_RSI    = 32
REVERSAL_MIN_DROP   = 3.0
REVERSAL_MAX_HOURS  = 2         # tightened from 4h — if no bounce in 2h, exit

# ── Shared ────────────────────────────────────────────────────
MIN_PRICE         = 0.001
SCAN_INTERVAL     = 60
# MIN_ALT_BUDGET is calculated at startup from actual balance (10% of starting balance)
# e.g. $50 account → $5 minimum, $200 account → $20 minimum
MIN_ALT_BUDGET    = None  # set in run() after fetching balance

TELEGRAM_TOKEN   = "8729639207:AAGR2ytuX36ocCVagQj-tGBE2QEkvrTiqQo"
TELEGRAM_CHAT_ID = "7058246374"

# ── AI Sentiment ──────────────────────────────────────────────
# Claude Haiku searches for latest news and returns a score -1.0 to +1.0.
# Applied as a score bonus/penalty after technical scoring passes threshold.
# Set ANTHROPIC_API_KEY as a Railway env var — bot works fine without it.
ANTHROPIC_API_KEY    = os.getenv("ANTHROPIC_API_KEY", "")
SENTIMENT_ENABLED    = bool(ANTHROPIC_API_KEY)
SENTIMENT_CACHE_MINS = 30       # reuse result for 30 min per symbol
SENTIMENT_MAX_BONUS  = 15       # max points added for very bullish sentiment (+1.0)
SENTIMENT_MAX_PENALTY= 20       # max points removed for very bearish sentiment (-1.0)
                                 # asymmetric: bad news hurts more than good news helps

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

# Rotation scan cooldown — don't hammer 40+ API calls every 5s
_last_rotation_scan    = 0.0
ROTATION_SCAN_INTERVAL = 30  # seconds between rotation scans

# New listings cache — scanning 60 symbols takes 3+ seconds, cache for 5 min
_new_listings_cache    = []
_new_listings_cache_at = 0.0
NEW_LISTINGS_CACHE_TTL = 300  # seconds

# Watchlist — top WATCHLIST_SIZE pairs pre-scored every WATCHLIST_TTL seconds
# During normal scans we only evaluate these, saving hundreds of API calls per hour
_watchlist             = []   # list of scored candidate dicts
_watchlist_at          = 0.0  # timestamp of last full rebuild

# Sentiment cache — {symbol: (score_float, fetched_at_timestamp)}
# Avoids calling Claude API on every scan cycle for the same coin
_sentiment_cache: dict = {}

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


def get_sentiment(symbol: str) -> tuple[float | None, str]:
    """
    Ask Claude Haiku to search for recent news on a coin and return a
    sentiment score from -1.0 (very bearish) to +1.0 (very bullish).

    Uses the Anthropic API with web_search enabled so Claude can look up
    actual current headlines rather than relying on training data.

    Returns:
        (score, summary_str) — score is None if API unavailable or errored.
        summary_str is a one-sentence reason, used in Telegram messages.

    Cached per symbol for SENTIMENT_CACHE_MINS to avoid hammering the API.
    Entire function is a no-op if ANTHROPIC_API_KEY is not set.
    """
    if not SENTIMENT_ENABLED:
        return None, ""

    # Check cache
    cached = _sentiment_cache.get(symbol)
    if cached:
        score, summary, fetched_at = cached
        if time.time() - fetched_at < SENTIMENT_CACHE_MINS * 60:
            return score, summary

    coin = symbol.replace("USDT", "").strip()
    try:
        response = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={
                "x-api-key":         ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01",
                "content-type":      "application/json",
            },
            json={
                "model":      "claude-haiku-4-5-20251001",
                "max_tokens": 200,
                "tools": [{"type": "web_search_20250305", "name": "web_search"}],
                "messages": [{
                    "role":    "user",
                    "content": (
                        f"Search for the latest news about {coin} cryptocurrency "
                        f"from the last 24 hours. Based on what you find, rate the "
                        f"current market sentiment for {coin}.\n\n"
                        f"Respond ONLY with valid JSON — no other text:\n"
                        f'{{ "score": <float from -1.0 to 1.0>, '
                        f'"summary": "<one sentence max 15 words>" }}\n\n'
                        f"Score guide: 1.0=very bullish, 0=neutral, -1.0=very bearish. "
                        f"Base it only on actual news you found, not general knowledge."
                    )
                }],
            },
            timeout=20,
        )
        response.raise_for_status()
        data = response.json()

        # Extract the text block from the response (may follow tool_use blocks)
        text = ""
        for block in data.get("content", []):
            if block.get("type") == "text":
                text = block["text"].strip()
                break

        if not text:
            return None, ""

        # Strip any accidental markdown fences
        text = text.replace("```json", "").replace("```", "").strip()
        parsed  = json.loads(text)
        score   = float(parsed["score"])
        summary = str(parsed.get("summary", ""))
        score   = max(-1.0, min(1.0, score))  # clamp to valid range

        _sentiment_cache[symbol] = (score, summary, time.time())
        log.info(f"🧠 Sentiment [{coin}]: {score:+.2f} — {summary}")
        return score, summary

    except Exception as e:
        log.debug(f"🧠 Sentiment fetch failed for {coin}: {e}")
        return None, ""


def sentiment_score_adjustment(symbol: str) -> tuple[float, str]:
    """
    Returns (score_delta, label_str) to add to the technical score.
    Positive = bullish bonus, negative = bearish penalty.
    Returns (0, "") if sentiment unavailable — never blocks a trade.
    """
    score, summary = get_sentiment(symbol)
    if score is None:
        return 0.0, ""

    if score >= 0:
        delta = round(score * SENTIMENT_MAX_BONUS,   1)
        label = f"🟢 sentiment {score:+.2f} (+{delta:.0f}pts)"
    else:
        # score is negative, SENTIMENT_MAX_PENALTY is positive → delta is negative (a penalty)
        delta = round(score * SENTIMENT_MAX_PENALTY, 1)
        label = f"🔴 sentiment {score:+.2f} ({delta:+.0f}pts)"

    return delta, label

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
    else: raise ValueError(f"Unsupported method: {method}")
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


def _score_for_watchlist(sym: str) -> dict | None:
    """
    Like evaluate_scalper_candidate but WITHOUT the score threshold cut-off.
    Used only for building the watchlist — we want a wide pool to monitor.
    Actual entry decisions re-score the top 5 with evaluate_scalper_candidate,
    which does apply the threshold.
    """
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

    atr     = calc_atr(df5m, period=SCALPER_ATR_PERIOD)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    return {
        "symbol": sym, "score": round(score, 2), "rsi": round(rsi, 2),
        "vol_ratio": round(vol_ratio, 2), "price": float(close.iloc[-1]),
        "atr_pct": round(atr_pct, 6),
    }


def build_watchlist(tickers: pd.DataFrame):
    """
    Score ALL eligible pairs and cache the top WATCHLIST_SIZE scorers.
    Called every WATCHLIST_TTL seconds (30 min) — this is the expensive scan.
    Between rebuilds, the scalper only evaluates pairs already on the watchlist.
    """
    global _watchlist, _watchlist_at

    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= SCALPER_MIN_PRICE]
    df = df[df["abs_change"]  >= SCALPER_MIN_CHANGE]
    df = df[~df["symbol"].isin(_api_blacklist)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(120)["symbol"].tolist()

    log.info(f"📋 [WATCHLIST] Building from {len(candidates)} candidates (full rescore)...")

    # Age filter — batch check new listings
    established = []
    for sym in candidates:
        try:
            data = public_get("/api/v3/klines", {"symbol": sym, "interval": "1d", "limit": 7})
            if len(data) >= 7:
                established.append(sym)
        except:
            established.append(sym)
        time.sleep(0.05)

    # Score all in parallel.
    # For watchlist building we use a lower threshold (half of entry threshold) so we
    # always have a pool of candidates to monitor even in quieter market conditions.
    # The entry scorer (find_scalper_opportunity) re-evaluates top 5 with fresh data anyway.
    WATCHLIST_MIN_SCORE = max(5, SCALPER_THRESHOLD // 2)
    scores = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        futures = {ex.submit(_score_for_watchlist, sym): sym for sym in established}
        for f in as_completed(futures):
            result = f.result()
            if result and result["score"] >= WATCHLIST_MIN_SCORE:
                scores.append(result)

    scores.sort(key=lambda x: x["score"], reverse=True)
    _watchlist    = scores[:WATCHLIST_SIZE]
    _watchlist_at = time.time()

    if not _watchlist:
        # Nothing qualified — retry in 5 min instead of waiting full TTL
        _watchlist_at = time.time() - WATCHLIST_TTL + 300
        log.warning("📋 [WATCHLIST] No pairs qualified — retrying in 5 min.")
        scanner_log("📋 Watchlist empty — will retry in 5min (market conditions)")
        return

    symbols = [s["symbol"] for s in _watchlist]
    log.info(f"📋 [WATCHLIST] {len(_watchlist)} pairs selected: {', '.join(symbols[:8])}{'...' if len(symbols) > 8 else ''}")
    scanner_log(f"📋 Watchlist rebuilt — top: {symbols[0] if symbols else 'none'} "
                f"({len(_watchlist)} pairs, next refresh in {WATCHLIST_TTL//60}min)")

    telegram(
        f"📋 <b>Watchlist Updated</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Top pairs: <b>{', '.join(symbols[:5])}</b>\n"
        f"{'...' + str(len(symbols)-5) + ' more' if len(symbols) > 5 else ''}\n"
        f"Next refresh: {WATCHLIST_TTL//60} min"
    )

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

    # Only score full 30pts if crossover happened in the last 2 candles (fresh signal).
    # A crossover from 40 minutes ago has already played out — only give trending credit.
    crossed_now    = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
    crossed_recent = (ema9.iloc[-2] > ema21.iloc[-2]) and (ema9.iloc[-3] <= ema21.iloc[-3])
    crossed        = crossed_now or crossed_recent
    ma_score       = 30 if crossed else (15 if ema9.iloc[-1] > ema21.iloc[-1] else 0)

    avg_vol   = volume.iloc[-20:-1].mean()
    vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
    vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
    score     = rsi_score + ma_score + vol_score

    if score < SCALPER_THRESHOLD:
        return None

    # Liquidity check — reject thin pairs that gap through SL on market sells.
    # Sum last 12 candles (~1h) × price = recent USDT volume.
    recent_vol_usdt = float(volume.iloc[-12:].sum()) * float(close.iloc[-1])
    if recent_vol_usdt < SCALPER_MIN_1H_VOL:
        log.debug(f"[SCALPER] Skip {sym} — thin (1h vol ${recent_vol_usdt:,.0f} < ${SCALPER_MIN_1H_VOL:,})")
        return None

    # Sentiment adjustment — applied after technical filters pass so we only
    # call the API on genuinely interesting candidates (saves cost + latency).
    sentiment_delta, sentiment_label = sentiment_score_adjustment(sym)
    score = round(score + sentiment_delta, 2)
    if sentiment_delta != 0:
        log.info(f"[SCALPER] {sym} sentiment adjusted: {sentiment_label} → final score {score}")
    # Re-check threshold after sentiment adjustment
    if score < SCALPER_THRESHOLD:
        log.info(f"[SCALPER] Skip {sym} — score dropped below threshold after sentiment ({score:.1f})")
        return None

    atr     = calc_atr(df5m, period=SCALPER_ATR_PERIOD)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    return {
        "symbol":    sym, "score": score, "rsi": round(rsi, 2),
        "vol_ratio": round(vol_ratio, 2), "price": float(close.iloc[-1]),
        "atr_pct":   round(atr_pct, 6),
        "sentiment": sentiment_delta if sentiment_delta != 0 else None,
    }


def find_scalper_opportunity(budget: float, exclude: set, open_symbols: set) -> dict | None:
    """
    Find the best scalper entry from the pre-built watchlist.
    The watchlist is rebuilt every WATCHLIST_TTL seconds with full scoring.
    Between rebuilds we just filter the cached list — very cheap.
    """
    global last_top_scalper

    if not _watchlist:
        log.info("🔍 [SCALPER] Watchlist empty — skipping until next rebuild.")
        return None

    # Filter watchlist: exclude open positions, cooldown symbols, blacklist
    # exclude is now a dict {symbol: cooldown_until_timestamp}
    now        = time.time()
    candidates = [
        s for s in _watchlist
        if s["symbol"] not in open_symbols
        and now >= exclude.get(s["symbol"], 0)
        and s["symbol"] not in _api_blacklist
    ]

    if not candidates:
        log.info("🔍 [SCALPER] All watchlist pairs excluded (open or blacklisted).")
        return None

    # Re-fetch quick price for the top candidates to make sure score is still valid
    # Only re-score the top 5 — avoids too many API calls between watchlist rebuilds
    refreshed = []
    for s in candidates[:5]:
        result = evaluate_scalper_candidate(s["symbol"])
        if result:
            refreshed.append(result)
        time.sleep(0.05)

    if not refreshed:
        # Fall back to cached scores if all re-scores failed
        refreshed = candidates[:5]

    refreshed.sort(key=lambda x: x["score"], reverse=True)
    best = refreshed[0]
    last_top_scalper = best

    age_mins = (time.time() - _watchlist_at) / 60
    scanner_log(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
                f"RSI: {best['rsi']} | ATR: {best['atr_pct']*100:.2f}% | "
                f"watchlist age: {age_mins:.0f}min")

    return pick_tradeable(refreshed, budget, "SCALPER")

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
    global _new_listings_cache, _new_listings_cache_at
    # Cache for NEW_LISTINGS_CACHE_TTL seconds — scanning 60 symbols takes 3+ seconds
    if time.time() - _new_listings_cache_at < NEW_LISTINGS_CACHE_TTL:
        # Filter cached results to remove any now open or excluded
        return [n for n in _new_listings_cache
                if n["symbol"] not in open_symbols and n["symbol"] not in exclude]

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

    _new_listings_cache    = new
    _new_listings_cache_at = time.time()
    log.info(f"🌙 [MOONSHOT] {len(new)} new listings ({MOONSHOT_MIN_DAYS}-{MOONSHOT_NEW_DAYS} days) — cached for {NEW_LISTINGS_CACHE_TTL}s")
    return [n for n in new if n["symbol"] not in open_symbols and n["symbol"] not in exclude]


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
            # Apply sentiment adjustment to qualifying moonshot candidates
            sentiment_delta, _ = sentiment_score_adjustment(sym)
            final_score = round(score + sentiment_delta, 2)
            if final_score < MOONSHOT_MIN_SCORE:
                log.info(f"[MOONSHOT] Skip {sym} — score dropped after sentiment ({final_score:.1f})")
                time.sleep(0.1); continue
            scores.append({
                "symbol": sym, "score": final_score, "rsi": round(rsi, 2),
                "vol_ratio": round(vol_ratio, 2), "price": float(close.iloc[-1]),
                "_df": df_k, "_is_new": is_new, "_1h_chg": round(change_1h or 0, 2),
                "sentiment": sentiment_delta if sentiment_delta != 0 else None,
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
        safe_opens  = opens.replace(0, np.nan)  # avoid division by zero on thin pairs
        candle_moves= (close - opens).abs() / safe_opens * 100
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


def get_actual_fills(symbol: str, since_ms: int, retries: int = 3) -> dict:
    """
    Fetch actual fill data from MEXC myTrades for a symbol since a timestamp.
    Retries up to `retries` times with 1s delay to allow fills to settle.
    Returns:
        avg_buy_price:  weighted average fill price of buy orders
        avg_sell_price: weighted average fill price of sell orders
        fee_usdt:       total fees paid in USDT equivalent
        cost_usdt:      total cost of buys (qty * price)
        revenue_usdt:   total revenue from sells (qty * price)
    """
    if PAPER_TRADE:
        return {}

    def wavg_price(trades):
        total_qty  = sum(float(t["qty"])      for t in trades)
        total_cost = sum(float(t["quoteQty"]) for t in trades)
        return (total_cost / total_qty) if total_qty > 0 else None

    def total_quote(trades):
        return sum(float(t["quoteQty"]) for t in trades)

    for attempt in range(retries):
        try:
            fills = private_get("/api/v3/myTrades", {
                "symbol":    symbol,
                "startTime": since_ms,
                "limit":     50,
            })
            if not fills:
                if attempt < retries - 1:
                    time.sleep(1)
                    continue
                return {}

            buys  = [f for f in fills if     f.get("isBuyer")]
            sells = [f for f in fills if not f.get("isBuyer")]

            # Fees — MEXC pays in the received asset, convert to USDT
            fee_usdt = 0.0
            for f in fills:
                commission = float(f.get("commission", 0))
                asset      = f.get("commissionAsset", "")
                if asset == "USDT":
                    fee_usdt += commission
                elif commission > 0:
                    # Approximate: fee in base asset × fill price
                    fee_usdt += commission * float(f.get("price", 0))

            result = {
                "avg_buy_price":  wavg_price(buys),
                "avg_sell_price": wavg_price(sells),
                "cost_usdt":      total_quote(buys),
                "revenue_usdt":   total_quote(sells),
                "fee_usdt":       round(fee_usdt, 6),
                "buy_count":      len(buys),
                "sell_count":     len(sells),
            }

            # Only return if we have at least a buy fill
            if result["avg_buy_price"] is not None:
                return result

        except Exception as e:
            log.debug(f"myTrades fetch failed {symbol}: {e}")

        if attempt < retries - 1:
            time.sleep(1)

    return {}

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

    # Record timestamp BEFORE placing the order so fills are captured reliably
    bought_at_ms = int(time.time() * 1000)

    buy_order = place_market_buy(symbol, qty, label)
    if not buy_order:
        return None

    # Fetch actual fill price — more accurate than the pre-order ticker price
    actual_fills = get_actual_fills(symbol, since_ms=bought_at_ms)
    actual_entry = actual_fills.get("avg_buy_price") or price
    actual_cost  = actual_fills.get("cost_usdt")     or notional
    if actual_fills.get("avg_buy_price"):
        log.info(f"[{label}] Actual fill: ${actual_entry:.6f} "
                 f"(ticker was ${price:.6f}, slippage: {(actual_entry/price-1)*100:+.3f}%)")
    else:
        log.info(f"[{label}] Using ticker price (myTrades unavailable): ${price:.6f}")

    actual_sl = sl_override_pct if sl_override_pct else sl_pct

    # SCALPER: TP = 3×ATR (same multiplier ratio as SL = 1.5×ATR → guaranteed 2:1 R:R)
    # MOONSHOT/REVERSAL: fixed pct TP passed in from caller
    if label == "SCALPER" and opp.get("atr_pct"):
        atr_tp_pct = opp["atr_pct"] * SCALPER_TP_ATR_MULT
        # Cap at SCALPER_TP_LIMIT (+10%) and floor at 2% (minimum worth the trade)
        atr_tp_pct = min(SCALPER_TP_LIMIT, max(0.02, atr_tp_pct))
        tp_price   = round_price_to_tick(actual_entry * (1 + atr_tp_pct), tick_size)
        used_tp_pct = atr_tp_pct
    else:
        tp_price    = round_price_to_tick(actual_entry * (1 + tp_pct), tick_size)
        used_tp_pct = tp_pct

    sl_price = round(actual_entry * (1 - actual_sl), 8)

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
        used_tp_pct = tp_pct
        tp_status   = "TP + SL bot-monitored ✅ (direct market sell)"

    trade = {
        "label":          label,
        "symbol":         symbol,
        "entry_price":    actual_entry,
        "entry_ticker":   price,
        "qty":            qty,
        "budget_used":    actual_cost,
        "bought_at_ms":   bought_at_ms,
        "tp_price":       tp_price,
        "sl_price":       sl_price,
        "tp_pct":         used_tp_pct,
        "sl_pct":         actual_sl,
        "tp_order_id":    tp_order_id,
        "highest_price":  actual_entry,
        "max_hours":      max_hours,
        "opened_at":      datetime.now(timezone.utc).isoformat(),
        "score":          opp.get("score", 0),
        "rsi":            opp.get("rsi", 0),
        "sentiment":      opp.get("sentiment"),  # sentiment score delta at entry
        # High-confidence trades get fast breakeven: SL moves to entry at +1.5%
        # preventing a winner from becoming a loser before the trailing stop kicks in
        "breakeven_act":  SCALPER_BREAKEVEN_ACT if (
                              label == "SCALPER" and
                              opp.get("score", 0) >= SCALPER_BREAKEVEN_SCORE
                          ) else None,
        "breakeven_done": False,   # flips True once SL has been moved to entry
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icon         = {"SCALPER":"🟢","MOONSHOT":"🌙","REVERSAL":"🔄"}.get(label,"🟢")
    timeout_line = f"Max hold:    {max_hours}h\n" if max_hours else ""

    breakeven_line = ""
    if trade.get("breakeven_act"):
        breakeven_line = f"Breakeven:   +{trade['breakeven_act']*100:.1f}% → SL moves to entry 🔒\n"

    slippage_line = ""
    if actual_fills.get("avg_buy_price") and abs(actual_entry - price) > 0.000001:
        slippage_pct  = (actual_entry / price - 1) * 100
        slippage_line = f"Slippage:    {slippage_pct:+.3f}%\n"

    sentiment_val = opp.get("sentiment")
    sentiment_line = ""
    if sentiment_val is not None:
        icon = "🟢" if sentiment_val > 0 else "🔴"
        sentiment_line = f"Sentiment:   {icon} {sentiment_val:+.1f}pts\n"

    if label == "SCALPER" and opp.get("atr_pct"):
        tp_display = f"TP (ATR×{SCALPER_TP_ATR_MULT:.0f}): <b>${tp_price:.6f}</b>  (+{used_tp_pct*100:.1f}%)\n"
    else:
        tp_display = f"Take profit: <b>${tp_price:.6f}</b>  (+{used_tp_pct*100:.0f}%)\n"

    log.info(f"{icon} [{label}] Opened {symbol} | ${actual_cost:.2f} | "
             f"Entry: {actual_entry:.6f} | TP: {tp_price:.6f} (+{used_tp_pct*100:.1f}%) | "
             f"SL: {sl_price:.6f} (-{actual_sl*100:.1f}%)")
    telegram(
        f"{icon} <b>Trade Opened — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${actual_cost:.2f} USDT</b>\n"
        f"Entry:       <b>${actual_entry:.6f}</b>\n"
        f"{slippage_line}"
        f"{sentiment_line}"
        f"{tp_display}"
        f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl*100:.1f}%) [market]\n"
        f"{breakeven_line}"
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
                # Order gone — but was it filled or cancelled?
                # If price never got close to TP, it was likely cancelled (e.g. restart)
                if price >= trade["tp_price"] * 0.995:
                    log.info(f"🎯 [{label}] TP limit filled: {symbol}")
                    return True, "TAKE_PROFIT"
                else:
                    log.warning(f"⚠️ [{label}] TP order vanished but price ${price:.6f} "
                                f"never reached TP ${trade['tp_price']:.6f} — "
                                f"order was cancelled not filled. Monitoring manually.")
                    trade["tp_order_id"] = None  # clear so we fall back to price polling
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
        # ── Breakeven trail (high-confidence trades only) ─────────
        # If score ≥ SCALPER_BREAKEVEN_SCORE and trade is up SCALPER_BREAKEVEN_ACT,
        # ratchet SL up to entry price — turns a potential loser into a break-even.
        # This fires once only, before the normal trailing stop activates.
        breakeven_act = trade.get("breakeven_act")
        if breakeven_act and not trade.get("breakeven_done") and pct >= breakeven_act * 100:
            if trade["sl_price"] < trade["entry_price"]:
                trade["sl_price"]      = trade["entry_price"]
                trade["breakeven_done"] = True
                log.info(f"🔒 [{label}] Breakeven locked: {symbol} | {pct:+.2f}% | "
                         f"SL moved to entry ${trade['entry_price']:.6f}")

        # ── Trailing stop ─────────────────────────────────────────
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
            except: body = {"msg": e.response.text if e.response else "no response"}

            code = body.get("code") if isinstance(body, dict) else None
            msg  = body.get("msg",  body) if isinstance(body, dict) else body
            log.error(f"🚨 [{label}] Market sell failed (code={code}): {msg}")

            # Code 30005 / -2010 = insufficient balance — position likely already closed
            # by the TP limit order filling at the same moment SL triggered
            if code in (30005, -2010) or "insufficient" in str(msg).lower() or "balance" in str(msg).lower():
                log.warning(f"⚠️ [{label}] {symbol} — position already closed on exchange "
                            f"(TP limit likely filled just before SL). Checking fills...")
                telegram(f"⚠️ [{label}] <b>{symbol}</b> ({reason})\n"
                         f"Market sell returned 'insufficient balance' — "
                         f"TP limit order may have filled simultaneously.\n"
                         f"Treating as TAKE_PROFIT and checking actual fills.")
                # Don't return False — fall through to record P&L from actual fills
                # The exit fills query below will pick up the TP limit fill

            elif code == 10007 or "not support" in str(msg).lower():
                _api_blacklist.add(symbol)
                log.warning(f"⚠️ [{label}] {symbol} not API-tradeable — blacklisted.")
                telegram(f"🚨 <b>Sell failed!</b> [{label}] {symbol} ({reason})\n"
                         f"Error: {str(msg)[:200]}\n"
                         f"Symbol blacklisted — close manually on MEXC.")
                return False

            else:
                telegram(f"🚨 <b>Sell failed!</b> [{label}] {symbol} ({reason})\n"
                         f"Code: {code} — {str(msg)[:200]}\n"
                         f"Close manually on MEXC.")
                return False

    # ── Fetch actual fill data for accurate P&L ───────────────
    exit_fills = {}
    if not PAPER_TRADE:
        bought_at_ms = trade.get("bought_at_ms", int(time.time() * 1000) - 86400_000)
        # For scalper TAKE_PROFIT, exchange limit may take a moment to settle
        retries    = 5 if (reason == "TAKE_PROFIT" and label == "SCALPER") else 3
        exit_fills = get_actual_fills(symbol, since_ms=bought_at_ms, retries=retries)

    # Fallback ticker price if fills unavailable
    try:
        ticker_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except:
        ticker_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]

    actual_entry  = exit_fills.get("avg_buy_price")   or trade["entry_price"]
    actual_exit   = exit_fills.get("avg_sell_price")  or ticker_price
    fee_usdt      = exit_fills.get("fee_usdt",  0.0)
    cost_usdt     = exit_fills.get("cost_usdt") or (actual_entry * trade["qty"])
    revenue_usdt  = exit_fills.get("revenue_usdt") or (actual_exit * trade["qty"])

    # True P&L = revenue − cost − fees
    pnl_usdt = round(revenue_usdt - cost_usdt - fee_usdt, 4)
    pnl_pct  = round(pnl_usdt / cost_usdt * 100, 4) if cost_usdt > 0 else 0.0

    if exit_fills.get("avg_sell_price"):
        log.info(f"[{label}] Fills: entry=${actual_entry:.6f} exit=${actual_exit:.6f} "
                 f"fees=${fee_usdt:.4f} P&L=${pnl_usdt:+.4f} ({pnl_pct:+.2f}%)")
    else:
        log.info(f"[{label}] Ticker exit ${ticker_price:.6f} (myTrades unavailable) "
                 f"P&L=${pnl_usdt:+.4f} ({pnl_pct:+.2f}%)")

    trade_history.append({
        **{k: v for k, v in trade.items() if not k.startswith("_")},
        "exit_price":    actual_exit,
        "exit_ticker":   ticker_price,
        "exit_reason":   reason,
        "closed_at":     datetime.now(timezone.utc).isoformat(),
        "fee_usdt":      fee_usdt,
        "cost_usdt":     round(cost_usdt, 4),
        "revenue_usdt":  round(revenue_usdt, 4),
        "pnl_pct":       pnl_pct,
        "pnl_usdt":      pnl_usdt,
        "fills_used":    bool(exit_fills.get("avg_sell_price")),
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

    fee_line   = f"Fees:    ${fee_usdt:.4f}\n" if fee_usdt > 0 else ""
    fills_note = "✅ actual fills" if exit_fills.get("avg_sell_price") else "⚠️ estimated"

    telegram(
        f"{emoji} <b>{reason_label} — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:    <b>{symbol}</b>\n"
        f"Entry:   ${actual_entry:.6f}\n"
        f"Exit:    <b>${actual_exit:.6f}</b>  [{fills_note}]\n"
        f"P&L:     <b>{pnl_pct:+.2f}%  (${pnl_usdt:+.2f})</b>\n"
        f"{fee_line}"
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

# ── Dust conversion ───────────────────────────────────────────

def convert_dust():
    """
    Convert all non-USDT spot balances worth less than $1 into MX token.
    Runs once per day at midnight alongside the daily summary.
    Skips safely if PAPER_TRADE, or if nothing qualifies.
    Rules: max 99 assets per call, each < $5 USDT value, 0.2% fee.
    """
    if PAPER_TRADE:
        return
    try:
        balances = private_get("/api/v3/account").get("balances", [])
        dust = []
        for b in balances:
            asset = b["asset"]
            free  = float(b.get("free", 0))
            if asset in ("USDT", "MX") or free <= 0:
                continue
            try:
                price = float(public_get("/api/v3/ticker/price",
                                         {"symbol": f"{asset}USDT"})["price"])
                value = free * price
                if 0 < value < 1.0:
                    dust.append(asset)
            except:
                pass  # no USDT pair for this asset — skip
            time.sleep(0.05)

        if not dust:
            log.info("🧹 Dust sweep: nothing to convert.")
            return

        log.info(f"🧹 Dust sweep: converting {len(dust)} assets: {dust}")
        result   = private_post("/api/v3/capital/convert",
                                {"asset": ",".join(dust[:99])})
        success  = result.get("successList", [])
        failed   = result.get("failedList",  [])
        total_mx = float(result.get("totalConvert", 0))
        fee_mx   = float(result.get("convertFee",   0))

        log.info(f"🧹 Dust converted: {len(success)} assets → {total_mx:.6f} MX (fee: {fee_mx:.6f} MX)")
        if success:
            telegram(
                f"🧹 <b>Dust Swept</b>\n"
                f"━━━━━━━━━━━━━━━\n"
                f"Converted: <b>{', '.join(success[:10])}"
                f"{'...' if len(success) > 10 else ''}</b>\n"
                f"Received:  <b>{total_mx:.6f} MX</b>\n"
                f"Fee:       {fee_mx:.6f} MX"
                + (f"\nFailed:    {', '.join(failed)}" if failed else "")
            )
    except Exception as e:
        log.debug(f"Dust sweep failed: {e}")

# ── Haiku helpers ─────────────────────────────────────────────

def ask_haiku(prompt: str, system: str = "", max_tokens: int = 500) -> str:
    """
    Core reusable call to Claude Haiku.
    Returns the text response, or "" on any failure.
    Does NOT use web search — for analysis tasks that only need trade data.
    """
    if not SENTIMENT_ENABLED:
        return ""
    try:
        messages = [{"role": "user", "content": prompt}]
        body = {
            "model":      "claude-haiku-4-5-20251001",
            "max_tokens": max_tokens,
            "messages":   messages,
        }
        if system:
            body["system"] = system

        r = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={
                "x-api-key":         ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01",
                "content-type":      "application/json",
            },
            json=body,
            timeout=30,
        )
        r.raise_for_status()
        for block in r.json().get("content", []):
            if block.get("type") == "text":
                return block["text"].strip()
    except Exception as e:
        log.debug(f"ask_haiku failed: {e}")
    return ""


def generate_daily_journal(today_trades: list, balance: float) -> str:
    """
    Pass today's closed trades to Haiku and ask for a plain-English analysis.
    Returns a formatted journal string ready to send as a Telegram message.
    Called once at midnight from send_daily_summary.
    """
    if not SENTIMENT_ENABLED or not today_trades:
        return ""

    # Build a compact trade summary — keep tokens low
    lines = []
    for t in today_trades:
        try:
            held = round(
                (datetime.fromisoformat(t['closed_at']) -
                 datetime.fromisoformat(t['opened_at'])).total_seconds() / 60
            )
        except Exception:
            held = 0
        lines.append(
            f"{t['symbol']} [{t['label']}] "
            f"entry={t.get('entry_price',0):.6f} exit={t.get('exit_price',0):.6f} "
            f"pnl={t.get('pnl_pct',0):+.2f}% (${t.get('pnl_usdt',0):+.2f}) "
            f"reason={t.get('exit_reason','?')} "
            f"score={t.get('score',0):.0f} rsi={t.get('rsi',0):.0f} "
            f"held={held}min"
        )

    system = (
        "You are a concise crypto trading analyst reviewing a day of automated bot trades. "
        "Be direct and specific. No generic advice. Focus on patterns in THIS data only. "
        "Never suggest changing the bot code directly — frame suggestions as observations."
    )

    prompt = (
        f"Today's closed trades ({len(today_trades)} total, balance ${balance:.2f}):\n\n"
        + "\n".join(lines)
        + "\n\nWrite a short journal entry (max 5 bullet points) covering:\n"
        "• What worked and what didn't — specific patterns, not generalities\n"
        "• Best and worst trade and why\n"
        "• Any time-of-day, RSI, or exit-reason patterns worth noting\n"
        "• One concrete observation for tomorrow\n\n"
        "Keep it under 200 words. Be honest, not cheerful."
    )

    analysis = ask_haiku(prompt, system=system, max_tokens=400)
    if not analysis:
        return ""

    wins   = [t for t in today_trades if t.get("pnl_pct", 0) > 0]
    losses = [t for t in today_trades if t.get("pnl_pct", 0) <= 0]
    total  = sum(t.get("pnl_usdt", 0) for t in today_trades)

    return (
        f"🧠 <b>Daily Journal</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{len(today_trades)} trades | {len(wins)}W {len(losses)}L | "
        f"P&L: <b>${total:+.2f}</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{analysis}"
    )

# ── Daily summary ─────────────────────────────────────────────

def send_daily_summary(balance: float):
    global last_daily_summary
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if last_daily_summary == today or datetime.now(timezone.utc).hour != 0:
        return
    last_daily_summary = today
    mode = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    # Sweep dust at midnight alongside the daily summary
    convert_dust()

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

    # ── AI journal — sent as a second message after raw stats ────
    try:
        today_trades = [t for t in trade_history if t.get("closed_at","")[:10] == today]
        journal = generate_daily_journal(today_trades, balance)
        if journal:
            telegram(journal[:4000])   # Telegram hard limit is 4096 chars
    except Exception as e:
        log.debug(f"Daily journal failed: {e}")

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
            msg      = update.get("message", {})
            raw_text = msg.get("text", "").strip()       # preserve case for /ask
            text     = raw_text.lower()
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
                    f"  Max: {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%\n"
                    f"  TP: ATR×{SCALPER_TP_ATR_MULT:.0f} (2:1 R:R, cap {SCALPER_TP_LIMIT*100:.0f}%)\n"
                    f"  SL: ATR×{SCALPER_ATR_MULT} | Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.1f}%\n"
                    f"  Watchlist: {len(_watchlist)} pairs | age: {(time.time()-_watchlist_at)/60:.0f}min\n"
                    f"\n🌙 <b>Moonshot</b>  [bot-monitored]\n"
                    f"  Max: {ALT_MAX_TRADES} trades | Min budget: ${MIN_ALT_BUDGET:.2f}\n"
                    f"  TP: +{MOONSHOT_TP*100:.0f}%  SL: -{MOONSHOT_SL*100:.0f}%  Max: {MOONSHOT_MAX_HOURS}h\n"
                    f"\n🔄 <b>Reversal</b>  [bot-monitored]\n"
                    f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  Max: {REVERSAL_MAX_HOURS}h\n"
                    f"\n🧠 Sentiment: {'✅ on' if SENTIMENT_ENABLED else '⚠️ off'}\n"
                    f"\n{'⏸️ PAUSED' if _paused else '▶️ RUNNING'}"
                )

            elif raw_text.startswith("/ask ") or raw_text.startswith("/ask@"):
                # /ask <question> — ask Haiku anything about the bot's recent trades
                question = raw_text.split(" ", 1)[1].strip() if " " in raw_text else ""
                if not question:
                    telegram("🧠 Usage: <code>/ask why am I losing on flat exits?</code>")
                elif not SENTIMENT_ENABLED:
                    telegram("🧠 <b>/ask</b> requires ANTHROPIC_API_KEY to be set.")
                else:
                    telegram("🧠 Thinking...")

                    # Build context from recent trade history (last 50 trades)
                    recent = trade_history[-50:] if len(trade_history) > 50 else trade_history
                    today  = datetime.now(timezone.utc).strftime("%Y-%m-%d")

                    context_lines = []
                    for t in recent:
                        context_lines.append(
                            f"{t.get('closed_at','?')[:16]} {t['symbol']} [{t['label']}] "
                            f"pnl={t.get('pnl_pct',0):+.2f}% reason={t.get('exit_reason','?')} "
                            f"score={t.get('score',0):.0f} rsi={t.get('rsi',0):.0f} "
                            f"held={round((datetime.fromisoformat(t['closed_at']) - datetime.fromisoformat(t['opened_at'])).total_seconds()/60)}min"
                        ) if t.get('closed_at') and t.get('opened_at') else None

                    context_lines = [l for l in context_lines if l]

                    # Open positions
                    open_ctx = []
                    for t in scalper_trades + alt_trades:
                        try:
                            px  = float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
                            pct = (px - t["entry_price"]) / t["entry_price"] * 100
                            open_ctx.append(f"{t['symbol']} [{t['label']}] currently {pct:+.2f}%")
                        except:
                            open_ctx.append(f"{t['symbol']} [{t['label']}]")

                    system = (
                        "You are a concise crypto trading analyst with access to a live bot's trade history. "
                        "Answer the user's question directly using only the data provided. "
                        "Be specific and honest. Keep answers under 150 words."
                    )

                    prompt = (
                        f"Bot trade history (last {len(context_lines)} closed trades):\n"
                        + "\n".join(context_lines[-30:])  # last 30 for token efficiency
                        + (f"\n\nCurrently open: {', '.join(open_ctx)}" if open_ctx else "")
                        + f"\n\nBalance: ${balance:.2f} USDT | Date: {today}\n\n"
                        f"User question: {question}"
                    )

                    answer = ask_haiku(prompt, system=system, max_tokens=300)
                    if answer:
                        # Escape HTML in both the question and Haiku's answer
                        safe_q = question.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
                        safe_a = answer.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
                        reply  = f"🧠 <b>Ask:</b> <i>{safe_q}</i>\n━━━━━━━━━━━━━━━\n{safe_a}"
                        telegram(reply[:4000])  # Telegram hard limit
                    else:
                        telegram("🧠 Couldn't get an answer — check logs.")

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
    global scalper_trades, alt_trades, _last_rotation_scan, _watchlist, _watchlist_at, MIN_ALT_BUDGET

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")

    _load_symbol_rules()
    reconcile_open_positions()

    # Build initial watchlist at startup
    log.info("📋 Building initial watchlist...")
    startup_tickers = fetch_tickers()
    build_watchlist(startup_tickers)

    startup_balance = get_available_balance()
    MIN_ALT_BUDGET  = round(startup_balance * 0.10, 2)
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT | Min alt budget: ${MIN_ALT_BUDGET:.2f}")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (max {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%)\n"
        f"  TP: ATR×{SCALPER_TP_ATR_MULT:.0f} (2:1 R:R) | SL: ATR×{SCALPER_ATR_MULT} (period {SCALPER_ATR_PERIOD})\n"
        f"  Entry threshold: score ≥ {SCALPER_THRESHOLD} | 1h vol ≥ ${SCALPER_MIN_1H_VOL:,}\n"
        f"  Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.1f}% trail\n"
        f"  Breakeven: score ≥ {SCALPER_BREAKEVEN_SCORE} → lock at +{SCALPER_BREAKEVEN_ACT*100:.1f}%\n"
        f"  Symbol cooldown: {SCALPER_SYMBOL_COOLDOWN//60}min after SL\n"
        f"  Daily loss limit: -{SCALPER_DAILY_LOSS_PCT*100:.0f}% of balance → circuit breaker\n"
        f"  Watchlist: top {WATCHLIST_SIZE} pairs, refresh every {WATCHLIST_TTL//60}min\n"
        f"\n🌙 <b>Moonshot</b> (max {ALT_MAX_TRADES} trades, 5% each) [bot-monitored]\n"
        f"  TP: +{MOONSHOT_TP*100:.0f}%  SL: -{MOONSHOT_SL*100:.0f}%  max {MOONSHOT_MAX_HOURS}h\n"
        f"  Min budget: ${MIN_ALT_BUDGET:.2f} (10% of balance)\n"
        f"\n🔄 <b>Reversal</b> (5%) [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  max {REVERSAL_MAX_HOURS}h\n"
        f"\n🧠 <b>AI Sentiment</b>: {'✅ enabled (Claude Haiku + web search)' if SENTIMENT_ENABLED else '⚠️ disabled (set ANTHROPIC_API_KEY)'}\n"
        f"  Cache: {SENTIMENT_CACHE_MINS}min | Bonus: +{SENTIMENT_MAX_BONUS}pts | Penalty: -{SENTIMENT_MAX_PENALTY}pts\n"
        f"\n<i>/status · /pnl · /logs · /config · /pause · /resume · /close · /ask</i>"
    )

    scalper_excluded = {}   # {symbol: cooldown_until_ts} — 30min cooldown after SL
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

            # Fetch tickers only when actively scanning for new entries
            scalper_needs_entry = not _paused and len(scalper_trades) < SCALPER_MAX_TRADES
            alt_needs_entry     = not _paused and len(alt_trades) < ALT_MAX_TRADES
            need_scan           = scalper_needs_entry or alt_needs_entry
            tickers             = fetch_tickers() if need_scan else None

            # Rebuild watchlist every WATCHLIST_TTL seconds (30 min)
            if time.time() - _watchlist_at >= WATCHLIST_TTL:
                log.info("📋 Watchlist TTL expired — rebuilding...")
                build_watchlist(tickers if tickers is not None else fetch_tickers())

            # ── Daily loss circuit breaker ────────────────────────
            today        = datetime.now(timezone.utc).strftime("%Y-%m-%d")
            daily_pnl    = sum(t["pnl_usdt"] for t in trade_history
                               if t.get("closed_at","")[:10] == today)
            loss_limit   = -(startup_balance * SCALPER_DAILY_LOSS_PCT)
            circuit_open = daily_pnl < loss_limit
            # Only log circuit state once every 5 minutes to avoid spam at 2s sleep
            if circuit_open and int(time.time()) % 300 < 3:
                log.info(f"🛑 Daily loss limit active (${daily_pnl:.2f} < ${loss_limit:.2f}) "
                         f"— no new scalper entries today")
            # Send Telegram alert exactly once when limit is first hit
            if circuit_open and not getattr(run, "_circuit_alerted_today", ""):
                run._circuit_alerted_today = today
                telegram(
                    f"🛑 <b>Daily loss limit hit</b>\n"
                    f"Session P&L: <b>${daily_pnl:.2f}</b> (limit: ${loss_limit:.2f})\n"
                    f"No new scalper entries until midnight UTC.\n"
                    f"Open positions are still monitored."
                )
            elif not circuit_open:
                run._circuit_alerted_today = ""  # reset for tomorrow

            # ── Scalper ───────────────────────────────────────
            budget = round(balance * SCALPER_BUDGET_PCT, 2)  # always defined before both branches

            if not _paused and not circuit_open and len(scalper_trades) < SCALPER_MAX_TRADES:
                opp = find_scalper_opportunity(budget,
                                               exclude=scalper_excluded,
                                               open_symbols=open_symbols)
                if opp:
                    sl_atr = opp["atr_pct"] * SCALPER_ATR_MULT
                    trade  = open_position(opp, budget, SCALPER_TP_LIMIT, SCALPER_SL,
                                           "SCALPER", sl_override_pct=sl_atr)
                    if trade:
                        scalper_trades.append(trade)
                        # Only remove THIS symbol's cooldown — other symbols keep theirs
                        scalper_excluded.pop(opp["symbol"], None)
            else:
                # At max capacity (or circuit open) — check for rotation every ROTATION_SCAN_INTERVAL
                now        = time.time()
                best_opp   = None
                best_score = 0
                if not circuit_open and now - _last_rotation_scan >= ROTATION_SCAN_INTERVAL:
                    _last_rotation_scan = now
                    best_opp   = find_scalper_opportunity(budget,
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
                        # SL/hard exits: add 30min cooldown. Rotation/TP: no penalty.
                        if reason in ("STOP_LOSS", "TRAILING_STOP", "FLAT_EXIT"):
                            scalper_excluded[trade["symbol"]] = (
                                time.time() + SCALPER_SYMBOL_COOLDOWN
                            )
                            log.info(f"⏳ [SCALPER] {trade['symbol']} in cooldown "
                                     f"for {SCALPER_SYMBOL_COOLDOWN//60}min after {reason}")
                        if close_position(trade, reason):
                            scalper_trades.remove(trade)
                            if reason == "ROTATION" and best_opp:
                                sl_atr = best_opp["atr_pct"] * SCALPER_ATR_MULT
                                new_t  = open_position(best_opp, budget, SCALPER_TP_LIMIT,
                                                       SCALPER_SL, "SCALPER",
                                                       sl_override_pct=sl_atr)
                                if new_t:
                                    scalper_trades.append(new_t)
                                    scalper_excluded.pop(best_opp["symbol"], None)

            # ── Alt (Moonshot / Reversal) ─────────────────────
            if not _paused and len(alt_trades) < ALT_MAX_TRADES:
                ideal  = round(total_value * MOONSHOT_BUDGET_PCT, 2)
                budget = min(ideal, balance)

                if budget < MIN_ALT_BUDGET:
                    log.info(f"💰 Alt budget ${budget:.2f} below minimum ${MIN_ALT_BUDGET:.2f} — skipping scan")
                else:
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
            # Scalper checks every 2s (thin altcoins can spike fast)
            # Alt trades every 5s (longer hold, less time-sensitive)
            # No open positions: full SCAN_INTERVAL before next scan
            if scalper_trades:
                time.sleep(2)
            elif alt_trades:
                time.sleep(5)
            else:
                time.sleep(SCAN_INTERVAL)

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
