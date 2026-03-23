"""
MEXC Trading Bot — 3 Strategies
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER  — Max 3 trades (30% cap, 1% risk) | Dynamic ATR TP/SL | 1H trend | 30min watchlist
  2. MOONSHOT — Max 2 trades (3%) | SL -8% | Partial TP +10% → 8% trail | RSI 35-70 gate
  3. REVERSAL — Max 2 trades (5%) | TP +4% | SL cap-candle anchor | Oversold bounce + vol capitulation
     Moonshot and Reversal share the alt slot.
"""

import time, hmac, hashlib, logging, logging.handlers, requests, json, os, threading, collections, re
import asyncio
import urllib.parse
from decimal import Decimal, ROUND_DOWN
import pandas as pd
import numpy as np
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = os.getenv("MEXC_API_KEY",    "your_api_key_here")
MEXC_API_SECRET = os.getenv("MEXC_API_SECRET", "your_api_secret_here")

PAPER_TRADE   = os.getenv("PAPER_TRADE", "False").lower() == "true"
PAPER_BALANCE = float(os.getenv("PAPER_BALANCE", "50"))

# ── Scalper (max 3 concurrent) ────────────────────────────────
SCALPER_MAX_TRADES   = int(os.getenv("SCALPER_MAX_TRADES",   "3"))
SCALPER_BUDGET_PCT   = float(os.getenv("SCALPER_BUDGET_PCT", "0.30"))  # max position cap
SCALPER_RISK_PER_TRADE = float(os.getenv("SCALPER_RISK_PER_TRADE", "0.01"))  # 1% of balance risked per trade
SCALPER_TRAIL_ACT    = 0.03      # trailing stop activates at +3%
SCALPER_TRAIL_PCT    = 0.015     # static fallback trail (used if trade has no trail_pct)
SCALPER_TRAIL_ATR_MULT = float(os.getenv("SCALPER_TRAIL_ATR_MULT", "1.5"))  # trail = 1.5× ATR at entry
SCALPER_TRAIL_MIN    = float(os.getenv("SCALPER_TRAIL_MIN",   "0.010"))     # floor 1.0%
SCALPER_TRAIL_MAX    = float(os.getenv("SCALPER_TRAIL_MAX",   "0.035"))     # ceiling 3.5%
SCALPER_CONFLUENCE_BONUS = float(os.getenv("SCALPER_CONFLUENCE_BONUS", "15"))
                                  # bonus pts when crossover + vol_ratio>2 + RSI rising simultaneously
SCALPER_ATR_MULT     = 1.5       # EMA21 distance fallback multiplier in dynamic SL
SCALPER_ATR_PERIOD   = 21        # ATR period — 21 candles smoother than 14, less SL hunting
SCALPER_FLAT_MINS    = 30
SCALPER_FLAT_RANGE   = 0.005
SCALPER_ROTATE_GAP   = 20
SCALPER_MIN_VOL      = 500_000
SCALPER_MIN_PRICE    = 0.01
SCALPER_MIN_CHANGE   = 0.1
SCALPER_THRESHOLD    = 40        # raised from 20 — only take high-quality entries
SCALPER_MAX_RSI      = 70
WATCHLIST_MIN_SCORE  = max(5, SCALPER_THRESHOLD // 2)  # wide net for watchlist candidates
# Breakeven trail — high-confidence trades (score ≥ this) move SL to entry at +1.5%
# Locks in a no-loss position before the normal trailing stop activates at +3%
SCALPER_BREAKEVEN_SCORE = 60     # score threshold for fast breakeven
SCALPER_BREAKEVEN_ACT   = 0.015  # move SL to entry once trade is up this much (+1.5%)
SCALPER_MIN_1H_VOL      = 50_000 # min $50k USDT volume in last 12×5m candles (~1h)
                                  # thin pairs gap hard through SL on market sells
SCALPER_SYMBOL_COOLDOWN = 1800   # seconds before re-entering a symbol after SL (30 min)
SCALPER_DAILY_LOSS_PCT  = 0.05   # stop new scalper entries if session down >5% of starting balance

SCALPER_EMA50_PENALTY  = float(os.getenv("SCALPER_EMA50_PENALTY", "200"))
                                  # score penalty per 1% coin is below 1H EMA50
                                  # e.g. 2% below EMA50 → -4pts. Same pattern as BTC_REGIME_EMA_PENALTY

# ── Dynamic TP — signal-aware, reality-capped ─────────────────
# Multiplier varies by what's driving the entry signal
SCALPER_TP_MULT_CROSSOVER = 2.5  # fresh EMA crossover — early in the move, room to run
SCALPER_TP_MULT_VOL_SPIKE = 1.8  # large vol spike — strong but often exhausts fast
SCALPER_TP_MULT_OVERSOLD  = 2.2  # RSI oversold bounce — moderate mean-reversion target
SCALPER_TP_MULT_DEFAULT   = 2.0  # trending entry, no dominant single signal
SCALPER_TP_CANDLE_MULT    = 4.0  # cap = N × avg candle body (reality check)
SCALPER_TP_MIN            = 0.025 # floor 2.5% — covers fees + slippage before profit starts
SCALPER_TP_MAX            = 0.08  # ceiling 8% — replaces the old 10% hard cap

# ── Dynamic SL — signal-aware, noise-floored ──────────────────
SCALPER_SL_MULT_VOL_SPIKE = 1.0  # tight — cut fast if vol spike turns fake
SCALPER_SL_MULT_OVERSOLD  = 1.0  # tight — oversold can always deepen
SCALPER_SL_MULT_HIGH_CONF = 1.8  # high-confidence multi-signal — give it room
SCALPER_SL_MULT_DEFAULT   = 1.3  # standard trending entry
SCALPER_SL_NOISE_MULT     = 2.0  # SL must be ≥ N × avg candle body (noise floor)
SCALPER_SL_MAX            = 0.04  # hard ceiling 4% — never risk more than this
SCALPER_SL_MIN            = 0.015 # hard floor 1.5% — gives trades breathing room on normal volatility

# ── Watchlist — universe of pairs pre-scored every 30 minutes ──
WATCHLIST_SIZE      = 30        # top N pairs by score to trade from
WATCHLIST_TTL       = 1800      # seconds between full rescores (30 min)

# ── Moonshot ──────────────────────────────────────────────────
ALT_MAX_TRADES      = 2
MOONSHOT_BUDGET_PCT   = float(os.getenv("MOONSHOT_BUDGET_PCT",   "0.03"))  # 3% — smaller size for wider SL
MOONSHOT_TP_INITIAL           = 0.15      # sets tp_price pre-partial-TP only; trailing stop takes over after
MOONSHOT_SL           = float(os.getenv("MOONSHOT_SL",           "0.08"))  # 8% — slippage can't kill the trade
MOONSHOT_TRAIL_PCT    = float(os.getenv("MOONSHOT_TRAIL_PCT",     "0.08"))  # trail 8% below highest after partial TP
MOONSHOT_MAX_VOL      = int(os.getenv("MOONSHOT_MAX_VOL", "5000000"))  # raised from 250k — was excluding most legitimate movers
MOONSHOT_MIN_VOL      = int(os.getenv("MOONSHOT_MIN_VOL", "50000"))  # raised from 5k — filters dangerous micro-caps
MOONSHOT_MIN_SCORE    = 30        # raised: need crossover OR strong vol burst, not just stale trend
MOONSHOT_MAX_RSI      = float(os.getenv("MOONSHOT_MAX_RSI",      "70"))   # overbought gate
MOONSHOT_MIN_RSI      = float(os.getenv("MOONSHOT_MIN_RSI",      "35"))   # freefall gate
MOONSHOT_RSI_ACCEL_MIN= float(os.getenv("MOONSHOT_RSI_ACCEL_MIN","60"))   # above this RSI, require acceleration
MOONSHOT_RSI_ACCEL_DELTA=float(os.getenv("MOONSHOT_RSI_ACCEL_DELTA","2")) # min RSI rise candle-over-candle to pass
MOONSHOT_MIN_NOTIONAL = float(os.getenv("MOONSHOT_MIN_NOTIONAL", "2.0"))
MOONSHOT_MAX_HOURS  = 2
MOONSHOT_MIN_DAYS   = 2
MOONSHOT_NEW_DAYS   = 14
MOONSHOT_MIN_VOL_BURST = 2.5
MOONSHOT_MIN_VOL_RATIO = float(os.getenv("MOONSHOT_MIN_VOL_RATIO", "1.2"))  # require ≥ avg volume
MOONSHOT_MIN_1H_VOL    = int(os.getenv("MOONSHOT_MIN_1H_VOL",   "10000"))  # min $10k in last hour — catches dead 24h vol
MOONSHOT_VOL_DIVISOR   = float(os.getenv("MOONSHOT_VOL_DIVISOR", "500000")) # vol-weighted sizing: budget_pct = min(3%, 24h_vol / divisor)
                                                                              # $500k vol → 1%, $1.5M → 3% (capped)

# ── Moonshot graduated timeout ─────────────────────────────────
# Hard clock replaced with P&L-aware timeouts:
MOONSHOT_TIMEOUT_FLAT_MINS   = 30    # exit if pct < 0.5% after this many minutes
MOONSHOT_TIMEOUT_MARGINAL_MINS= 60   # exit if pct < 5.0% after this many minutes
MOONSHOT_TIMEOUT_MAX_MINS    = 120   # absolute ceiling regardless of P&L
# Mid-hold vol re-check — if volume collapses the pump is over
MOONSHOT_VOL_CHECK_MINS      = 15    # start checking vol after this many minutes held
MOONSHOT_VOL_COLLAPSE_RATIO  = 0.5   # exit if current vol < 50% of avg AND trade barely up
# Partial TP — capture first leg reliably, let remainder run to full target
MOONSHOT_PARTIAL_TP_PCT      = 0.10  # sell first half at +10% (raised from 6% — better R:R with wider SL)
MOONSHOT_PARTIAL_TP_RATIO    = 0.50  # fraction to sell at stage 1 (50%)
MOONSHOT_BREAKEVEN_ACT       = float(os.getenv("MOONSHOT_BREAKEVEN_ACT", "0.04"))  # move SL to entry at +4%

# ── Reversal ──────────────────────────────────────────────────
REVERSAL_TP              = 0.040  # +4%
REVERSAL_SL              = 0.020  # -2% fallback (overridden by cap-candle anchor)
REVERSAL_MIN_VOL         = 100_000
REVERSAL_MAX_RSI         = 32
REVERSAL_MIN_DROP        = 3.0
REVERSAL_MAX_HOURS       = 2
REVERSAL_BOUNCE_RECOVERY = 0.30   # current candle must reclaim ≥30% of prior red candle body
REVERSAL_VOL_RECOVERY    = 1.20   # bounce candle volume must be ≥ 1.2× 20-candle avg
                                   # (confirms buyers stepping in, not just dead-cat)
REVERSAL_CAP_SL_BUFFER   = 0.005  # place SL 0.5% below capitulation candle low
# Partial TP — capture reliable first bounce leg, protect remainder at breakeven
REVERSAL_PARTIAL_TP_PCT  = 0.025  # sell first half at +2.5%
REVERSAL_PARTIAL_TP_RATIO= 0.50   # fraction to sell at stage 1 (50%)

# ── Shared ────────────────────────────────────────────────────
MIN_PRICE         = 0.001
SCAN_INTERVAL     = 60
STATE_FILE        = "state.json"  # persists open positions + history across restarts

TELEGRAM_TOKEN   = os.getenv("TELEGRAM_TOKEN",   "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")

# ── HTTP reliability ───────────────────────────────────────────
HTTP_RETRIES           = 3        # retry GET requests this many times
HTTP_RETRY_DELAY       = 1.0     # base backoff seconds (doubles each retry)
HTTP_TRANSIENT_CODES   = {429, 500, 502, 503, 504}  # retry on these
KLINE_CACHE_TTL        = 30      # seconds to cache kline data — avoids duplicate
                                  # fetches when evaluate and score run close together
MAX_KLINE_CACHE        = 500     # evict stale entries when cache exceeds this size

# ── API health ─────────────────────────────────────────────────
API_FAIL_THRESHOLD     = 5       # consecutive failures before escalating sleep
API_FAIL_SLEEP_BASE    = 30      # base sleep seconds on repeated API failure
API_FAIL_SLEEP_MAX     = 300     # max sleep seconds (5 min cap)
FILL_QTY_TOLERANCE     = 1.02   # sell qty capped at buy qty × this (2% for fee rounding)

# ── Entry quality gates ────────────────────────────────────────
SCALPER_MAX_SPREAD     = 0.004   # skip pair if bid/ask spread > 0.4% (slippage risk)
SCALPER_MAX_CORRELATION= 0.85    # skip if 20-candle return correlation with open
                                  # position > 0.85 (avoids correlated simultaneous SLs)
SCALPER_MIN_ATR_PCT    = 0.003   # skip pair if ATR/price < 0.3% — choppy, TP unreachable
MAX_CONSECUTIVE_LOSSES = int(os.getenv("MAX_CONSECUTIVE_LOSSES", "3"))
STREAK_AUTO_RESET_MINS = int(os.getenv("STREAK_AUTO_RESET_MINS", "60"))  # auto-clear streak after this many minutes
WIN_RATE_CB_WINDOW     = int(os.getenv("WIN_RATE_CB_WINDOW",     "10"))
WIN_RATE_CB_THRESHOLD  = float(os.getenv("WIN_RATE_CB_THRESHOLD","0.30"))
WIN_RATE_CB_PAUSE_MINS = int(os.getenv("WIN_RATE_CB_PAUSE_MINS", "60"))
MAX_EXPOSURE_PCT       = float(os.getenv("MAX_EXPOSURE_PCT",     "0.80"))
MOONSHOT_MAX_SPREAD    = 0.008   # skip moonshot if spread > 0.8% — pump entries fill worse

# ── BTC regime filter ──────────────────────────────────────────
# If BTC drops sharply in the last 5m candle the whole market is risk-off.
# Entering a scalper position in that window almost guarantees an SL trigger.
BTC_REGIME_DROP        = 0.02    # hard block: scalper paused if BTC last 5m candle < -2%
BTC_REGIME_EMA_PERIOD  = 100     # EMA period for trend score penalty (100×5m = 8h)
BTC_REGIME_EMA_PENALTY = float(os.getenv("BTC_REGIME_EMA_PENALTY", "300"))
                                  # score penalty per 1% BTC is below EMA100
                                  # e.g. BTC 2% below EMA → -6pts on candidate score
BTC_REGIME_VOL_MULT    = 2.0     # hard block: scalper paused if BTC ATR > N× average
BTC_PANIC_DROP         = 0.05    # pause ALL strategies (incl. alts) if BTC drops > 5% in one candle

# ── AI Sentiment ──────────────────────────────────────────────
# Claude Haiku searches for latest news and returns a score -1.0 to +1.0.
# Applied as a score bonus/penalty after technical scoring passes threshold.
# Set ANTHROPIC_API_KEY as a Railway env var — bot works fine without it.
ANTHROPIC_API_KEY    = os.getenv("ANTHROPIC_API_KEY", "")
SENTIMENT_ENABLED    = bool(ANTHROPIC_API_KEY)
# Web search costs significantly more than plain Haiku calls.
# Disable by default — only /ask and daily journal (plain Haiku) remain active.
# Set WEB_SEARCH_ENABLED=true in Railway to re-enable sentiment + social boost.
WEB_SEARCH_ENABLED   = os.getenv("WEB_SEARCH_ENABLED", "false").lower() == "true"
SENTIMENT_CACHE_MINS = 30       # reuse result for 30 min per symbol
SENTIMENT_MAX_BONUS  = 15       # max points added for very bullish sentiment (+1.0)
SENTIMENT_MAX_PENALTY= 20       # max points removed for very bearish sentiment (-1.0)
                                 # asymmetric: bad news hurts more than good news helps

# ── Moonshot social sentiment ──────────────────────────────────
# Two-layer AI signal for moonshot discovery:
# 1. Trending scan — Haiku searches for socially trending coins every N minutes,
#    adds them to the candidate pool before technical scoring runs.
# 2. Social boost — per-symbol search for influencer/Reddit buzz on candidates
#    that pass technical scoring, applied as a score bonus on top of news sentiment.
MOONSHOT_SOCIAL_SCAN_MINS  = int(os.getenv("MOONSHOT_SOCIAL_SCAN_MINS",  "99999"))  # disabled by default; set to 30 to enable
MOONSHOT_SOCIAL_MAX_COINS  = int(os.getenv("MOONSHOT_SOCIAL_MAX_COINS",  "10"))
MOONSHOT_SOCIAL_BOOST_MAX  = int(os.getenv("MOONSHOT_SOCIAL_BOOST_MAX",  "20"))
MOONSHOT_SOCIAL_CACHE_MINS = int(os.getenv("MOONSHOT_SOCIAL_CACHE_MINS", "20"))

# ═══════════════════════════════════════════════════════════════
BASE_URL = "https://api.mexc.com"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.handlers.RotatingFileHandler(
            "bot.log", maxBytes=10_000_000, backupCount=5
        ),
    ]
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
_scanner_log_buffer   = collections.deque(maxlen=5)  # rolling window, auto-evicts oldest
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

# Sentiment cache — {symbol: (score_float, summary, fetched_at_timestamp)}
_sentiment_cache: dict = {}
_sentiment_lock        = threading.Lock()  # protects writes; reads are safe without lock

# Kline cache — {(symbol, interval, limit): (df, fetched_at)}
# Short TTL so evaluate + score don't double-fetch the same data
_kline_cache: dict = {}
_kline_cache_lock  = threading.Lock()  # protects writes from 8-thread watchlist builder

# Thread-local HTTP sessions — requests.Session is NOT thread-safe.
# Each thread gets its own session for connection pooling without contention.
_thread_local = threading.local()

# API health tracking — detect sustained outages and escalate sleep
_api_fail_count   = 0    # consecutive public_get failures (reset on success)
_api_fail_alerted = False # True once we've sent the "MEXC down?" Telegram message

# Consecutive loss streak — pause scalper entries after MAX_CONSECUTIVE_LOSSES SLs
# Complements daily circuit breaker: catches short bad-regime windows, not just daily limit
_consecutive_losses   = 0
_win_rate_pause_until = 0.0  # epoch ts; all entries blocked until this if win rate too low
_streak_paused_at     = 0.0  # epoch ts when streak CB last triggered (for auto-reset)

# Semaphore for moonshot parallel scan — limits concurrent kline fetches to avoid 429s
_moonshot_scan_sem = threading.Semaphore(5)

# Exclusion dicts — module-level so save_state() always has access to current values
# without needing them passed as arguments from run()
_scalper_excluded: dict = {}  # {symbol: cooldown_until_ts}
_alt_excluded:     set  = set()

# Moonshot social sentiment caches
_trending_coins:      list  = []   # [(symbol, reason_str), ...] from last trending scan
_trending_coins_at:   float = 0.0  # timestamp of last trending scan
_social_boost_cache:  dict  = {}   # {symbol: (boost_float, summary, fetched_at)}
_btc_ema_gap:         float = 0.0  # latest BTC vs EMA100 gap (negative = below); used in watchlist display

# ── WebSocket price monitor ────────────────────────────────────
# Maintains a live price cache for all open positions via MEXC's
# miniTicker WebSocket stream. check_exit reads from this cache
# instead of making a REST call per trade per cycle — turning
# up-to-2s polling latency into real-time price updates.
#
# Requires: pip install websockets
#
# Falls back to REST automatically when:
#   - WS not yet connected (startup window)
#   - Price not updated for > WS_STALE_SECS seconds
#   - Symbol not subscribed (shouldn't happen, but handled)

WS_URL          = "wss://wbs-api.mexc.com/ws"
WS_PING_SECS    = 20    # send PING every N seconds to keep connection alive
WS_STALE_SECS   = 60    # fall back to REST if price not updated within this window

_live_prices: dict = {}     # {symbol: (price_float, updated_at_ts)}
_ws_lock           = threading.Lock()


def ws_price(symbol: str) -> float | None:
    """
    Return the latest WebSocket price for symbol, or None if unavailable.
    Returns None if the price is stale (not updated in WS_STALE_SECS),
    triggering a REST fallback in the caller.
    """
    with _ws_lock:
        entry = _live_prices.get(symbol)
    if entry is None:
        return None
    price, updated_at = entry
    if time.time() - updated_at > WS_STALE_SECS:
        return None
    return price


async def _ws_loop():
    """
    Async loop: connect to MEXC WebSocket, subscribe to miniTicker for
    all open positions, update _live_prices on every push.
    Reconnects automatically with exponential backoff on any error.
    """
    try:
        import websockets
    except ImportError:
        log.error("🔌 'websockets' library not installed — WS monitor disabled. "
                  "Add 'websockets' to requirements.txt and redeploy.")
        return

    backoff      = 2
    last_wanted  = set()  # tracks previous subscription set — only sync on change

    while True:
        # No open positions — no point connecting, MEXC closes idle connections in 30s
        wanted = {t["symbol"] for t in list(scalper_trades) + list(alt_trades)}
        if not wanted:
            await asyncio.sleep(5)
            continue

        try:
            async with websockets.connect(
                WS_URL,
                ping_interval=None,   # we send our own pings
                close_timeout=5,
                open_timeout=10,
            ) as ws:
                log.info("🔌 WS price monitor connected")
                backoff    = 2  # reset on successful connect
                subscribed = set()
                last_ping  = time.time()

                while True:
                    # ── Sync subscriptions to open positions ──────
                    # Snapshot the trade lists to avoid racing with the main thread
                    # which can append/remove trades concurrently.
                    wanted = {t["symbol"] for t in list(scalper_trades) + list(alt_trades)}

                    if wanted != last_wanted:
                        new_subs = wanted - subscribed
                        if new_subs:
                            await ws.send(json.dumps({
                                "method": "SUBSCRIPTION",
                                "params": [f"spot@public.miniTicker.v3.api@{s}" for s in new_subs],
                            }))
                            subscribed |= new_subs
                            log.info(f"🔌 WS subscribed: {sorted(new_subs)}")

                        old_subs = subscribed - wanted
                        if old_subs:
                            await ws.send(json.dumps({
                                "method": "UNSUBSCRIPTION",
                                "params": [f"spot@public.miniTicker.v3.api@{s}" for s in old_subs],
                            }))
                            subscribed -= old_subs
                            log.debug(f"🔌 WS unsubscribed: {sorted(old_subs)}")

                        last_wanted = wanted

                    # ── Keepalive ping ────────────────────────────
                    if time.time() - last_ping >= WS_PING_SECS:
                        await ws.send(json.dumps({"method": "PING"}))
                        last_ping = time.time()

                    # ── Read one message (0.5s timeout) ───────────
                    try:
                        raw = await asyncio.wait_for(ws.recv(), timeout=0.5)
                    except asyncio.TimeoutError:
                        continue  # no message this window, loop again

                    # Skip binary frames (protobuf — shouldn't occur on non-.pb channel)
                    if isinstance(raw, bytes):
                        continue

                    try:
                        msg = json.loads(raw)
                    except Exception:
                        continue

                    # miniTicker format: {"s": "BTCUSDT", "d": {"p": "36474.74", ...}}
                    d   = msg.get("d", {})
                    sym = msg.get("s") or d.get("s")
                    px  = d.get("p")
                    if sym and px:
                        with _ws_lock:
                            _live_prices[sym] = (float(px), time.time())

        except Exception as e:
            log.warning(f"🔌 WS error ({type(e).__name__}: {e}) — reconnect in {backoff}s")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 60)


def _start_ws_monitor():
    """
    Launch the WebSocket price monitor in a daemon background thread.
    Uses a dedicated asyncio event loop so it doesn't interfere with
    the synchronous main loop.
    """
    def _run():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            loop.run_until_complete(_ws_loop())
        except Exception as e:
            log.error(f"🔌 WS monitor thread crashed: {e}")
        finally:
            loop.close()

    t = threading.Thread(target=_run, daemon=True, name="ws-price-monitor")
    t.start()
    log.info("🔌 WebSocket price monitor starting...")


# ── State persistence ──────────────────────────────────────────

def save_state():
    """
    Atomically persist all runtime state to STATE_FILE.
    Called after every open_position, execute_partial_tp, close_position, and on shutdown.
    On restart, load_state() re-hydrates from this file so monitoring continues.
    """
    try:
        payload = {
            "scalper_trades":       scalper_trades,
            "alt_trades":           alt_trades,
            "trade_history":        trade_history,
            "consecutive_losses":   _consecutive_losses,
            "win_rate_pause_until": _win_rate_pause_until,
            "streak_paused_at":     _streak_paused_at,
            "scalper_excluded":     _scalper_excluded,
            "alt_excluded":         list(_alt_excluded),
            "api_blacklist":        list(_api_blacklist),
            "saved_at":             datetime.now(timezone.utc).isoformat(),
        }
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(payload, f, default=str)
        os.replace(tmp, STATE_FILE)  # atomic on POSIX; avoids corrupt half-writes
    except Exception as e:
        log.warning(f"State save failed: {e}")


def load_state() -> tuple[list, list, list, int, float, float, dict, set, set]:
    """
    Load persisted state from STATE_FILE.
    Returns (scalper_trades, alt_trades, trade_history,
             consecutive_losses, win_rate_pause_until, streak_paused_at,
             scalper_excluded, alt_excluded, api_blacklist).
    Returns empty defaults if file is missing or unreadable.
    """
    try:
        if not os.path.exists(STATE_FILE):
            return [], [], [], 0, 0.0, 0.0, {}, set(), set()
        with open(STATE_FILE) as f:
            d = json.load(f)
        age = (datetime.now(timezone.utc) -
               datetime.fromisoformat(d.get("saved_at", "2000-01-01T00:00:00+00:00"))
               ).total_seconds()
        log.info(f"📂 Loading state (saved {age/60:.0f}min ago): "
                 f"{len(d.get('scalper_trades',[]))} scalper, "
                 f"{len(d.get('alt_trades',[]))} alt trades, "
                 f"{len(d.get('trade_history',[]))} history entries")
        return (
            d.get("scalper_trades",       []),
            d.get("alt_trades",           []),
            d.get("trade_history",        []),
            d.get("consecutive_losses",   0),
            d.get("win_rate_pause_until", 0.0),
            d.get("streak_paused_at",     0.0),
            d.get("scalper_excluded",     {}),
            set(d.get("alt_excluded",     [])),
            set(d.get("api_blacklist",    [])),
        )
    except Exception as e:
        log.warning(f"State load failed ({e}) — starting fresh")
        return [], [], [], 0, 0.0, 0.0, {}, set(), set()

def _get_session() -> requests.Session:
    """Return a thread-local requests.Session, creating one if needed."""
    if not hasattr(_thread_local, "session"):
        s = requests.Session()
        s.headers.update({"Accept": "application/json"})
        _thread_local.session = s
    return _thread_local.session

# ── Telegram ───────────────────────────────────────────────────

def telegram(msg: str, parse_mode: str = "HTML"):
    """Send a Telegram message. Falls back to plain text on HTML parse errors."""
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        log.debug("Telegram not configured — skipping message")
        return
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    for attempt in range(2):
        try:
            r = _get_session().post(
                url,
                json={"chat_id": TELEGRAM_CHAT_ID, "text": msg, "parse_mode": parse_mode},
                timeout=8,
            )
            if r.ok:
                return
            body = r.json() if r.content else {}
            desc = body.get("description", "")
            if r.status_code == 400 and "parse" in desc.lower():
                # HTML parse error — strip all tags and retry as plain text
                log.debug("Telegram HTML parse error — retrying as plain text")
                r2 = _get_session().post(
                    url,
                    json={"chat_id": TELEGRAM_CHAT_ID, "text": re.sub(r'<[^>]+>', '', msg), "parse_mode": ""},
                    timeout=8,
                )
                if r2.ok:
                    return
                log.warning(f"Telegram plain-text fallback also failed: {r2.text[:100]}")
                return  # give up — don't retry again
            log.warning(f"Telegram send failed (HTTP {r.status_code}): {r.text[:200]}")
        except Exception as e:
            if attempt == 0:
                log.debug(f"Telegram send failed, retrying: {e}")
                time.sleep(1)
            else:
                log.warning(f"Telegram send failed after retry: {e}")

def scanner_log(msg: str):
    _scanner_log_buffer.append(f"[{datetime.now(timezone.utc).strftime('%H:%M:%S')}] {msg}")
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
    if not SENTIMENT_ENABLED or not WEB_SEARCH_ENABLED:
        return None, ""

    # Check cache
    cached = _sentiment_cache.get(symbol)
    if cached:
        score, summary, fetched_at = cached
        if time.time() - fetched_at < SENTIMENT_CACHE_MINS * 60:
            return score, summary

    coin = symbol.replace("USDT", "").strip()
    try:
        response = _get_session().post(
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

        # Strip markdown fences, then use regex to find the first {...} JSON object.
        # This handles preamble text like "Here is the sentiment: {...}" that breaks
        # a direct json.loads() call even after stripping fences.
        text = text.replace("```json", "").replace("```", "").strip()
        m = re.search(r'\{[^{}]+\}', text, re.DOTALL)
        if not m:
            log.debug(f"🧠 No JSON object found in sentiment response [{coin}]: {text[:120]}")
            return None, ""
        try:
            parsed = json.loads(m.group())
        except json.JSONDecodeError:
            log.debug(f"🧠 Bad sentiment JSON from Haiku [{coin}]: {m.group()[:120]}")
            return None, ""

        score   = float(parsed["score"])
        summary = str(parsed.get("summary", ""))
        score   = max(-1.0, min(1.0, score))  # clamp to valid range

        with _sentiment_lock:
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

def get_trending_coins() -> list[tuple[str, str]]:
    """
    Option B — Proactive trending scan.
    Ask Haiku to search for coins currently trending on social media.
    Returns [(symbol_without_USDT, reason), ...]. Cached for
    MOONSHOT_SOCIAL_SCAN_MINS. Returns [] if disabled or on error.
    """
    global _trending_coins, _trending_coins_at
    if not SENTIMENT_ENABLED or not WEB_SEARCH_ENABLED:
        return []
    if time.time() - _trending_coins_at < MOONSHOT_SOCIAL_SCAN_MINS * 60:
        return _trending_coins

    prompt = (
        f"Search Reddit (r/CryptoCurrency, r/SatoshiStreetBets, r/altcoin), "
        f"crypto Twitter/X, and Telegram channel summaries right now. "
        f"Find up to {MOONSHOT_SOCIAL_MAX_COINS} cryptocurrency coins "
        f"being hyped, trending, or pumped by influencers in the last few hours. "
        f"Focus on small/unknown coins, not BTC/ETH/SOL.\n\n"
        f"Respond ONLY with valid JSON — no other text:\n"
        f'{{"coins": [{{"symbol": "<TICKER without USDT>", '
        f'"reason": "<max 10 words why trending>"}}, ...]}}\n\n'
        f"Only include coins with genuine social momentum right now. "
        f"If nothing credible found, return {{\"coins\": []}}."
    )

    # ask_haiku doesn't support web_search — call directly with tool
    try:
        response = _get_session().post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key": ANTHROPIC_API_KEY,
                     "anthropic-version": "2023-06-01",
                     "content-type": "application/json"},
            json={"model": "claude-haiku-4-5-20251001", "max_tokens": 400,
                  "tools": [{"type": "web_search_20250305", "name": "web_search"}],
                  "messages": [{"role": "user", "content": prompt}]},
            timeout=25,
        )
        response.raise_for_status()
        text = ""
        for block in response.json().get("content", []):
            if block.get("type") == "text":
                text = block["text"].strip()
                break
        if not text:
            return _trending_coins

        text = text.replace("```json", "").replace("```", "").strip()
        # Non-greedy match of outermost {...} — avoids swallowing nested structures
        m = re.search(r'\{.*?\}', text, re.DOTALL)
        if not m:
            # Fallback: find the array directly
            m = re.search(r'\[.*?\]', text, re.DOTALL)
            parsed = {"coins": json.loads(m.group())} if m else {"coins": []}
        else:
            parsed = json.loads(m.group())

        result = []
        for c in parsed.get("coins", [])[:MOONSHOT_SOCIAL_MAX_COINS]:
            sym    = str(c.get("symbol", "")).upper().strip().replace("USDT", "")
            reason = str(c.get("reason", ""))
            if sym and len(sym) >= 2:
                result.append((sym, reason))

        _trending_coins    = result
        _trending_coins_at = time.time()
        if result:
            log.info(f"🔥 Trending scan: {[s for s, _ in result]}")
        return result

    except Exception as e:
        log.debug(f"🔥 Trending scan failed: {e}")
        return _trending_coins


def get_social_boost(symbol: str) -> tuple[float, str]:
    """
    Option A — Per-symbol social sentiment boost.
    For a moonshot candidate that passed technical scoring, search for
    influencer mentions, Reddit posts, and community hype.
    Returns (boost_points, summary) — boost is 0–MOONSHOT_SOCIAL_BOOST_MAX.
    Cached per symbol for MOONSHOT_SOCIAL_CACHE_MINS.
    Uses _moonshot_scan_sem so parallel scorer threads don't flood the API.
    Returns (0, "") if disabled or on error.
    """
    if not SENTIMENT_ENABLED or not WEB_SEARCH_ENABLED:
        return 0.0, ""

    cached = _social_boost_cache.get(symbol)
    if cached:
        boost, summary, fetched_at = cached
        if time.time() - fetched_at < MOONSHOT_SOCIAL_CACHE_MINS * 60:
            return boost, summary

    coin = symbol.replace("USDT", "").strip()
    prompt = (
        f"Search for {coin} cryptocurrency on Reddit, Twitter/X, and Telegram right now. "
        f"Look for: influencer posts, community hype, viral threads, 'gem' recommendations, "
        f"or coordinated buying signals.\n\n"
        f"Rate the SOCIAL MOMENTUM (not fundamentals) from 0.0 to 1.0.\n\n"
        f"Respond ONLY with valid JSON — no other text:\n"
        f'{{"social_score": <0.0 to 1.0>, "summary": "<one sentence max 12 words>"}}\n\n'
        f"0.0 = no social activity found, 1.0 = massive viral hype right now. "
        f"Base it only on what you actually found, not general knowledge."
    )

    # Use the semaphore so parallel scorer threads don't all fire Anthropic calls at once
    with _moonshot_scan_sem:
        # ask_haiku doesn't support web_search tools — call directly
        try:
            response = _get_session().post(
                "https://api.anthropic.com/v1/messages",
                headers={"x-api-key": ANTHROPIC_API_KEY,
                         "anthropic-version": "2023-06-01",
                         "content-type": "application/json"},
                json={"model": "claude-haiku-4-5-20251001", "max_tokens": 200,
                      "tools": [{"type": "web_search_20250305", "name": "web_search"}],
                      "messages": [{"role": "user", "content": prompt}]},
                timeout=20,
            )
            response.raise_for_status()
            text = ""
            for block in response.json().get("content", []):
                if block.get("type") == "text":
                    text = block["text"].strip()
                    break
        except Exception as e:
            log.debug(f"🔥 Social boost failed for {coin}: {e}")
            return 0.0, ""

    if not text:
        return 0.0, ""

    text = text.replace("```json", "").replace("```", "").strip()
    m = re.search(r'\{[^{}]+\}', text, re.DOTALL)
    if not m:
        return 0.0, ""

    try:
        parsed  = json.loads(m.group())
        raw     = float(parsed.get("social_score", 0.0))
        score   = max(0.0, min(1.0, raw))
        summary = str(parsed.get("summary", ""))
        boost   = round(score * MOONSHOT_SOCIAL_BOOST_MAX, 1)
        _social_boost_cache[symbol] = (boost, summary, time.time())
        if boost > 0:
            log.info(f"🔥 Social boost [{coin}]: +{boost:.0f}pts — {summary}")
        return boost, summary
    except Exception:
        return 0.0, ""


def public_get(path, params=None):
    """GET with retry on transient errors (5xx, 429, network timeouts).
    Tracks consecutive failures and escalates sleep + sends Telegram on sustained outage."""
    global _api_fail_count, _api_fail_alerted
    url = BASE_URL + path
    for attempt in range(HTTP_RETRIES):
        try:
            r = _get_session().get(url, params=params or {}, timeout=10)
            if r.status_code in HTTP_TRANSIENT_CODES:
                if attempt < HTTP_RETRIES - 1:
                    wait = (2 ** attempt) * HTTP_RETRY_DELAY
                    if r.status_code == 429:
                        wait = max(wait, float(r.headers.get("Retry-After", wait)))
                    log.debug(f"HTTP {r.status_code} on GET {path} — retry {attempt+1} in {wait:.1f}s")
                    time.sleep(wait)
                    continue
            r.raise_for_status()
            # Success — reset failure tracking
            if _api_fail_count > 0:
                log.info(f"✅ MEXC API recovered after {_api_fail_count} failures")
            _api_fail_count   = 0
            _api_fail_alerted = False
            return r.json()
        except (requests.ConnectionError, requests.Timeout) as e:
            if attempt < HTTP_RETRIES - 1:
                wait = (2 ** attempt) * HTTP_RETRY_DELAY
                log.debug(f"Network error on GET {path} — retry {attempt+1} in {wait:.1f}s: {e}")
                time.sleep(wait)
            else:
                _api_fail_count += 1
                sleep_secs = min(API_FAIL_SLEEP_BASE * _api_fail_count, API_FAIL_SLEEP_MAX)
                log.warning(f"⚠️ MEXC API fail #{_api_fail_count} — sleeping {sleep_secs}s")
                if _api_fail_count >= API_FAIL_THRESHOLD and not _api_fail_alerted:
                    _api_fail_alerted = True
                    telegram(
                        f"⚠️ <b>MEXC API unreachable</b>\n"
                        f"{_api_fail_count} consecutive failures on {path}\n"
                        f"Bot is pausing between retries. Open positions still monitored."
                    )
                time.sleep(sleep_secs)
                raise
    raise requests.RequestException(f"GET {path} failed after {HTTP_RETRIES} attempts")

def _sign_request(params: dict, path: str) -> tuple[str, dict]:
    """Build a signed URL + headers for a private MEXC endpoint. Always uses fresh timestamp."""
    p         = {**params, "timestamp": int(time.time() * 1000)}  # never mutate caller's dict
    qs        = urllib.parse.urlencode(p)
    signature = hmac.new(MEXC_API_SECRET.encode(), qs.encode(), hashlib.sha256).hexdigest()
    url       = f"{BASE_URL}{path}?{qs}&signature={signature}"
    headers   = {"X-MEXC-APIKEY": MEXC_API_KEY}
    return url, headers

def private_request(method, path, params=None):
    """
    Signed MEXC API request.
    GET: retries with fresh timestamp on transient errors (safe — read-only).
    POST/DELETE: single attempt — order actions must never be duplicated.
    """
    params  = params or {}
    session = _get_session()

    if method == "GET":
        for attempt in range(HTTP_RETRIES):
            url, headers = _sign_request(params, path)
            try:
                r = session.get(url, headers=headers, timeout=10)
                if r.status_code in HTTP_TRANSIENT_CODES and attempt < HTTP_RETRIES - 1:
                    wait = (2 ** attempt) * HTTP_RETRY_DELAY
                    if r.status_code == 429:
                        wait = max(wait, float(r.headers.get("Retry-After", wait)))
                    log.debug(f"HTTP {r.status_code} on private GET {path} — retry in {wait:.1f}s")
                    time.sleep(wait)
                    continue
                r.raise_for_status()
                return r.json()
            except (requests.ConnectionError, requests.Timeout) as e:
                if attempt < HTTP_RETRIES - 1:
                    wait = (2 ** attempt) * HTTP_RETRY_DELAY
                    log.debug(f"Network error on private GET {path} — retry in {wait:.1f}s: {e}")
                    time.sleep(wait)
                else:
                    raise
    elif method == "POST":
        url, headers = _sign_request(params, path)
        r = session.post(url, headers=headers, timeout=10)
        r.raise_for_status()
        return r.json()
    elif method == "DELETE":
        url, headers = _sign_request(params, path)
        r = session.delete(url, headers=headers, timeout=10)
        r.raise_for_status()
        return r.json()
    else:
        raise ValueError(f"Unsupported method: {method}")

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
    """Round price down to nearest tick using Decimal to avoid float precision errors."""
    if not tick_size or float(tick_size) == 0:
        return round(price, 8)
    d_price = Decimal(str(price))
    d_tick  = Decimal(str(tick_size))
    rounded = (d_price / d_tick).to_integral_value(rounding=ROUND_DOWN) * d_tick
    # Derive decimal places directly from the Decimal exponent — handles all representations
    # including scientific notation (e.g. 1e-6) and trailing zeros (e.g. 0.00000100)
    decimals = max(0, -rounded.normalize().as_tuple().exponent)
    return round(float(rounded), decimals)

def calc_qty(budget: float, price: float, step_size: float) -> float:
    """
    Calculate floored quantity using Decimal to avoid float representation errors.
    e.g. math.floor(100.0 / 0.1) = floor(999.999...) = 999 due to float imprecision.
    Decimal("100.0") / Decimal("0.1") = exactly 1000.
    """
    if price <= 0 or step_size <= 0:
        return 0.0
    d_budget = Decimal(str(budget))
    d_price  = Decimal(str(price))
    d_step   = Decimal(str(step_size))
    raw      = d_budget / d_price
    floored  = (raw / d_step).to_integral_value(rounding=ROUND_DOWN) * d_step
    return float(floored)

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
    """True Range with Wilder's smoothing (EWM alpha=1/period).
    Adapts faster than simple rolling mean — tighter SLs after pump exhaustion."""
    high       = df["high"]
    low        = df["low"]
    prev_close = df["close"].shift(1)
    tr = pd.concat([
        high - low,
        (high - prev_close).abs(),
        (low  - prev_close).abs(),
    ], axis=1).max(axis=1)
    atr = tr.ewm(alpha=1.0 / period, adjust=False).mean().iloc[-1]
    return float(atr) if not np.isnan(atr) else 0.0

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
    # Short-TTL cache — avoids duplicate fetches when evaluate and score
    # run within seconds of each other on the same symbol
    cache_key = (symbol, interval, limit)
    cached    = _kline_cache.get(cache_key)
    if cached:
        df_cached, fetched_at = cached
        if time.time() - fetched_at < KLINE_CACHE_TTL:
            return df_cached if (df_cached is not None and len(df_cached) >= min_len) else None

    df = None
    try:
        data = public_get("/api/v3/klines", {"symbol": symbol, "interval": interval, "limit": limit})
        if not data:
            with _kline_cache_lock:
                _kline_cache[cache_key] = (None, time.time())
            return None
        df = pd.DataFrame(data)
        df.columns = range(len(df.columns))
        df = df.rename(columns={0:"open_time", 1:"open", 2:"high", 3:"low", 4:"close", 5:"volume"})
        for col in ["open","high","low","close","volume"]:
            df[col] = pd.to_numeric(df[col], errors="coerce")
        df = df.dropna(subset=["close","volume"])
        if len(df) < min_len:
            df = None
    except Exception as e:
        log.debug(f"Klines error {symbol}/{interval}: {e}")
        df = None

    with _kline_cache_lock:
        # Evict stale entries if cache is too large — prefer eviction over blind clear
        # so that still-valid entries survive
        if len(_kline_cache) >= MAX_KLINE_CACHE:
            now        = time.time()
            stale_keys = [k for k, (_, t) in _kline_cache.items()
                          if now - t > KLINE_CACHE_TTL]
            for k in stale_keys:
                del _kline_cache[k]
            # If nothing was stale (all fresh), clear half to prevent runaway growth
            if len(_kline_cache) >= MAX_KLINE_CACHE:
                for k in list(_kline_cache.keys())[:MAX_KLINE_CACHE // 2]:
                    del _kline_cache[k]
        _kline_cache[cache_key] = (df, time.time())
    return df

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


def _score_scalper(sym: str, strict: bool = False) -> dict | None:
    """
    Score a symbol for scalper consideration.

    strict=False (watchlist): lower threshold, no sentiment, no volatility filter.
    strict=True  (entry):     full filters — threshold, sentiment, ATR check.
    Both paths return the same dict shape.
    """
    df_1h = parse_klines(sym, interval="60m", limit=60)
    if df_1h is None:
        return None
    ema50_1h  = calc_ema(df_1h["close"], 50).iloc[-1]
    ema50_gap = (float(df_1h["close"].iloc[-1]) / float(ema50_1h) - 1)
    # Convert to penalty instead of hard block — coins slightly below EMA50 can still
    # qualify if their signal is strong enough. Deep below = penalised out naturally.
    ema50_penalty = round(max(0.0, -ema50_gap) * SCALPER_EMA50_PENALTY, 1)

    df5m = parse_klines(sym, interval="5m", limit=60)
    if df5m is None:
        return None

    close  = df5m["close"]
    volume = df5m["volume"]
    rsi    = calc_rsi(close)
    if np.isnan(rsi) or rsi > SCALPER_MAX_RSI:
        return None
    rsi_prev  = calc_rsi(close.iloc[:-1])
    rsi_delta = rsi - rsi_prev if not np.isnan(rsi_prev) else 0.0

    rsi_score      = max(0, 40 - rsi) if rsi < 50 else 0
    ema9           = calc_ema(close, 9)
    ema21          = calc_ema(close, 21)
    crossed_now    = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
    crossed_recent = (ema9.iloc[-2] > ema21.iloc[-2]) and (ema9.iloc[-3] <= ema21.iloc[-3])
    crossed        = crossed_now or crossed_recent
    ma_score       = 30 if crossed else (15 if ema9.iloc[-1] > ema21.iloc[-1] else 0)
    avg_vol        = volume.iloc[-20:-1].mean()
    vol_ratio      = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
    vol_score      = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0

    # Confluence bonus — non-linear reward when all three signals align simultaneously.
    # A fresh crossover alone scores 30. A vol spike alone scores 30. But when both
    # fire together with rising RSI momentum, this is a regime shift, not three
    # independent signals — deserves a material bonus on top.
    confluence_bonus = (SCALPER_CONFLUENCE_BONUS
                        if crossed_now and vol_ratio > 2.0 and rsi_delta > 0
                        else 0.0)

    score          = rsi_score + ma_score + vol_score + confluence_bonus - ema50_penalty

    threshold = SCALPER_THRESHOLD if strict else max(5, SCALPER_THRESHOLD // 2)
    if score < threshold:
        if ema50_penalty > 0:
            log.debug(f"[SCALPER] Skip {sym} — EMA50 penalty {ema50_penalty:.1f}pts "
                      f"({ema50_gap*100:.1f}% below EMA50)")
        return None

    sentiment_delta = 0.0
    if strict:
        recent_vol_usdt = float(volume.iloc[-12:].sum()) * float(close.iloc[-1])
        if recent_vol_usdt < SCALPER_MIN_1H_VOL:
            log.debug(f"[SCALPER] Skip {sym} — thin "
                      f"(1h vol ${recent_vol_usdt:,.0f} < ${SCALPER_MIN_1H_VOL:,})")
            return None
        # Only fetch sentiment when score is near the threshold — if already well above
        # or below, sentiment can't change the decision and the API call is wasted.
        if score > SCALPER_THRESHOLD - 5:
            sentiment_delta, sentiment_label = sentiment_score_adjustment(sym)
            score = round(score + sentiment_delta, 2)
            if sentiment_delta != 0:
                log.info(f"[SCALPER] {sym} sentiment: {sentiment_label} → score {score}")
        if score < SCALPER_THRESHOLD:
            log.info(f"[SCALPER] Skip {sym} — below threshold after sentiment ({score:.1f})")
            return None

    atr     = calc_atr(df5m, period=SCALPER_ATR_PERIOD)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    if strict and atr_pct < SCALPER_MIN_ATR_PCT:
        log.debug(f"[SCALPER] Skip {sym} — low volatility "
                  f"(ATR {atr_pct*100:.3f}% < {SCALPER_MIN_ATR_PCT*100:.1f}%)")
        return None

    curr_close     = float(close.iloc[-1])
    ema21_dist_pct = max(0.0, (curr_close - float(ema21.iloc[-1])) / curr_close) if curr_close > 0 else 0.0
    opens          = df5m["open"]
    safe_close     = close.replace(0, np.nan)
    raw_candle_pct = ((close - opens).abs() / safe_close).iloc[-10:].mean()
    avg_candle_pct = float(raw_candle_pct) if not np.isnan(raw_candle_pct) else atr_pct

    result = {
        "symbol":          sym,
        "score":           round(score, 2),
        "rsi":             round(rsi, 2),
        "rsi_delta":       round(rsi_delta, 2),
        "confluence_bonus":confluence_bonus,
        "vol_ratio":       round(vol_ratio, 2),
        "ema50_gap":       round(ema50_gap * 100, 2),
        "ema50_penalty":   ema50_penalty,
        "price":           curr_close,
        "atr_pct":         round(atr_pct, 6),
        # ATR-based trail width — stored here, transferred to trade dict at open_position.
        # Computed once at scoring time so check_exit never needs to re-fetch klines.
        "trail_pct":       round(min(SCALPER_TRAIL_MAX,
                                     max(SCALPER_TRAIL_MIN, atr_pct * SCALPER_TRAIL_ATR_MULT)), 6),
        "crossed_now":     crossed_now,
        "ema21_dist_pct":  round(ema21_dist_pct, 6),
        "avg_candle_pct":  round(avg_candle_pct, 6),
    }
    if strict:
        result["sentiment"] = sentiment_delta if sentiment_delta != 0 else None
    return result


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

    # Age filter — exclude symbols that are too new for scalping.
    # Reuse the moonshot new-listings cache (already populated) rather than
    # fetching 120 daily klines one by one, which blocks for ~6 seconds.
    new_listing_syms = {n["symbol"] for n in _new_listings_cache}
    established = [s for s in candidates if s not in new_listing_syms]
    log.info(f"📋 [WATCHLIST] {len(established)} established pairs after age filter "
             f"({len(candidates) - len(established)} new listings excluded)")

    # Score all in parallel — entry scorer re-evaluates top 5 with fresh data anyway
    scores = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(_score_scalper, sym, False): sym for sym in established}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result and result["score"] >= WATCHLIST_MIN_SCORE:
                    scores.append(result)
            except Exception as e:
                sym = futures[f]
                log.debug(f"[WATCHLIST] Score failed for {sym}: {e}")

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
    log.info(f"📋 [WATCHLIST] {len(_watchlist)} pairs: {', '.join(symbols[:8])}{'...' if len(symbols) > 8 else ''}")
    scanner_log(f"📋 Watchlist rebuilt — top: {symbols[0]} ({len(_watchlist)} pairs)")

    top   = _watchlist[0]
    top_line = (f"{top['symbol']} "
                f"score={top['score']:.0f}"
                + (" 🔥" if top.get("confluence_bonus") else "")
                + f" RSI={top['rsi']:.0f} ATR={top['atr_pct']*100:.2f}% vol={top['vol_ratio']:.1f}×"
                + (f" trail={top['trail_pct']*100:.1f}%" if top.get('trail_pct') else ""))

    # Explain why we're not entering right now
    why_not = []
    if _paused:
        why_not.append("bot paused")
    if len(scalper_trades) >= SCALPER_MAX_TRADES:
        why_not.append(f"at max {SCALPER_MAX_TRADES} trades")
    if top["score"] < SCALPER_THRESHOLD:
        why_not.append(f"score {top['score']:.0f} < threshold {SCALPER_THRESHOLD}")
    if _btc_ema_gap < -0.005:  # only mention if meaningfully below (> 0.5%)
        penalty = round(abs(_btc_ema_gap) * BTC_REGIME_EMA_PENALTY, 1)
        why_not.append(f"BTC {_btc_ema_gap*100:.1f}% below EMA (-{penalty:.0f}pts penalty)")
    if top.get("ema50_penalty", 0) > 0:
        why_not.append(f"coin EMA50 -{top['ema50_penalty']:.0f}pts ({top['ema50_gap']:.1f}% below)")
    status_line = f"Holding off: {', '.join(why_not)}" if why_not else "Ready to enter ✅"

    telegram(
        f"📋 <b>Watchlist Updated</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Top: <b>{top_line}</b>\n"
        f"{status_line}\n"
        f"{'Other: ' + ', '.join(symbols[1:5]) + ('...' if len(symbols) > 5 else '') + chr(10) if len(symbols) > 1 else ''}"
        f"Next refresh: {WATCHLIST_TTL//60} min"
    )

# ── Scanner: Scalper ───────────────────────────────────────────


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
        result = _score_scalper(s["symbol"], strict=True)
        if result:
            refreshed.append(result)
        time.sleep(0.05)

    if not refreshed:
        # All re-scores failed — API issue or market conditions changed.
        # Do NOT fall back to cached watchlist scores: those only passed the
        # lower watchlist threshold (score ≥ 20) and may not meet entry threshold (≥ 40).
        # Better to skip this cycle than enter on stale, under-threshold data.
        log.info("🔍 [SCALPER] All re-scores returned None — skipping entry this cycle.")
        return None

    refreshed.sort(key=lambda x: x["score"], reverse=True)
    best = refreshed[0]
    last_top_scalper = best

    age_mins = (time.time() - _watchlist_at) / 60
    scanner_log(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
                f"RSI: {best['rsi']} | ATR: {best['atr_pct']*100:.2f}% | "
                f"watchlist age: {age_mins:.0f}min")

    # 🟢 Correlation filter — skip candidate if its returns are highly correlated
    # with an already-open scalper position. Correlated positions SL simultaneously
    # when BTC dumps, concentrating drawdown. Only check if we have open trades.
    if scalper_trades and len(refreshed) > 0:
        filtered = []
        for cand in refreshed:
            try:
                df_cand = parse_klines(cand["symbol"], interval="5m", limit=25, min_len=20)
                if df_cand is None:
                    filtered.append(cand)
                    continue
                cand_returns = df_cand["close"].pct_change().dropna().iloc[-20:]
                too_correlated = False
                for open_trade in scalper_trades:
                    df_open = parse_klines(open_trade["symbol"], interval="5m", limit=25, min_len=20)
                    if df_open is None:
                        continue
                    open_returns = df_open["close"].pct_change().dropna().iloc[-20:]
                    # Align by length in case of small differences
                    n   = min(len(cand_returns), len(open_returns))
                    corr = float(np.corrcoef(cand_returns.iloc[-n:], open_returns.iloc[-n:])[0, 1])
                    if not np.isnan(corr) and corr > SCALPER_MAX_CORRELATION:
                        log.info(f"[SCALPER] Skip {cand['symbol']} — corr {corr:.2f} "
                                 f"with open {open_trade['symbol']}")
                        too_correlated = True
                        break
                if not too_correlated:
                    filtered.append(cand)
            except Exception:
                filtered.append(cand)  # on any error, don't block the candidate

        refreshed = filtered if filtered else refreshed  # fallback if all correlated

    return pick_tradeable(refreshed, budget, "SCALPER")

# ── Scanner: Moonshot ──────────────────────────────────────────

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

    # Sort by absolute price change to surface anything moving hard in either direction.
    # We deliberately drop the 24h priceChangePercent directional filter here —
    # in a down market a coin can pump +100% in an hour but still show negative 24h change,
    # so filtering on 24h change misses the exact moves moonshot exists to catch.
    # The kline scorer (EMA crossover + vol ratio) handles quality filtering.
    momentum_candidates = (df.assign(abs_change=df["priceChangePercent"].abs())
                             .sort_values("abs_change", ascending=False)
                             .head(20)["symbol"].tolist())

    new_listings = find_new_listings(tickers, exclude=exclude, open_symbols=open_symbols)
    new_symbols  = [n["symbol"] for n in new_listings]

    # Option B — add socially trending coins to the candidate pool.
    # get_trending_coins() is cached so this is cheap on most cycles.
    trending       = get_trending_coins()
    trending_syms  = []
    trending_reasons = {}
    all_ticker_syms = set(df["symbol"])
    for coin, reason in trending:
        sym = f"{coin}USDT"
        if (sym in all_ticker_syms
                and sym not in open_symbols
                and sym not in exclude
                and sym not in _api_blacklist):
            trending_syms.append(sym)
            trending_reasons[sym] = reason
    if trending_syms:
        log.info(f"🔥 [MOONSHOT] Adding {len(trending_syms)} trending coins: {trending_syms}")

    all_candidates = list(dict.fromkeys(new_symbols + trending_syms + momentum_candidates))
    log.info(f"🌙 [MOONSHOT] {len(all_candidates)} candidates "
             f"({len(new_symbols)} new + {len(trending_syms)} trending + {len(momentum_candidates)} momentum)")
    if not all_candidates:
        return None

    # Score candidates in parallel with a Semaphore to avoid MEXC rate-limit (429).
    # Max 5 concurrent kline fetches — aggressive enough to be fast, gentle on the API.
    def _score_moonshot(sym: str) -> dict | None:
        with _moonshot_scan_sem:
            is_new = sym in new_symbols
            interval = "60m" if is_new else "15m"
            df_k = parse_klines(sym, interval=interval, limit=60)
            if df_k is None:
                return None
            close  = df_k["close"]
            volume = df_k["volume"]
            rsi      = calc_rsi(close)
            if np.isnan(rsi):
                return None
            rsi_prev  = calc_rsi(close.iloc[:-1])  # RSI one candle ago
            rsi_delta = rsi - rsi_prev if not np.isnan(rsi_prev) else 0.0
            if rsi > MOONSHOT_MAX_RSI:
                return None  # overbought — entering after the bulk of the move
            if rsi < MOONSHOT_MIN_RSI:
                return None  # freefall — coin declining, not starting to pump
            # Tiered RSI momentum gate:
            # RSI ≤ MOONSHOT_RSI_ACCEL_MIN: allow freely — early in the move
            # RSI > MOONSHOT_RSI_ACCEL_MIN: require RSI still accelerating (rsi_delta > threshold)
            # This lets through DEXE/VVV-style moves while blocking late overbought entries
            if rsi > MOONSHOT_RSI_ACCEL_MIN and rsi_delta < MOONSHOT_RSI_ACCEL_DELTA:
                return None  # RSI elevated but decelerating — likely topping out
            rsi_score = max(0, 40 - rsi) if rsi < 50 else 0
            ema9  = calc_ema(close, 9)
            ema21 = calc_ema(close, 21)
            crossed   = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
            # Only score fresh crossover — "EMA above but crossed hours ago" is a mid-pump entry.
            # A stale uptrend with no crossover scores 0 here; vol_score must carry it instead.
            ma_score  = 30 if crossed else 0
            avg_vol   = volume.iloc[-20:-1].mean()
            vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
            vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
            if vol_ratio < MOONSHOT_MIN_VOL_RATIO:
                return None  # below average volume — no momentum
            # Recent 1h liquidity check — mirrors SCALPER_MIN_1H_VOL.
            # A coin can have $200k 24h volume but $190k happened 18h ago.
            # Candle count depends on interval: 4×15m = 1h, 1×60m = 1h.
            recent_candles = 1 if is_new else 4  # 60m interval for new listings, 15m otherwise
            recent_1h_vol = float(volume.iloc[-recent_candles:].sum()) * float(close.iloc[-1])
            if recent_1h_vol < MOONSHOT_MIN_1H_VOL:
                log.debug(f"[MOONSHOT] Skip {sym} — dead recently "
                          f"(1h vol ${recent_1h_vol:,.0f} < ${MOONSHOT_MIN_1H_VOL:,})")
                return None
            score     = rsi_score + ma_score + vol_score
            if score < MOONSHOT_MIN_SCORE:
                return None
            # Only apply sentiment/social when score is near threshold — reduces cost
            # significantly since most candidates fail well before sentiment matters.
            if score > MOONSHOT_MIN_SCORE - 5:
                sentiment_delta, _ = sentiment_score_adjustment(sym)
                social_boost, social_summary = get_social_boost(sym)
            else:
                sentiment_delta, social_boost, social_summary = 0.0, 0.0, ""
            final_score = round(score + sentiment_delta + social_boost, 2)
            if final_score < MOONSHOT_MIN_SCORE:
                return None
            # 24h change — kept for logging only, not used as a filter.
            # EMA crossover + vol_ratio in the scorer already enforce upward momentum.
            row = df[df["symbol"] == sym]
            change_1h = float(row["priceChangePercent"].iloc[0]) if not row.empty else 0.0
            return {
                "symbol":       sym,
                "score":        final_score,
                "rsi":          round(rsi, 2),
                "rsi_delta":    round(rsi_delta, 2),
                "vol_ratio":    round(vol_ratio, 2),
                "vol_1h_usdt":  round(recent_1h_vol, 0),
                "price":        float(close.iloc[-1]),
                "_df":          df_k,
                "_is_new":      is_new,
                "_is_trending": sym in trending_syms,
                "_trend_reason":trending_reasons.get(sym, ""),
                "_1h_chg":      round(change_1h or 0, 2),
                "sentiment":    sentiment_delta if sentiment_delta != 0 else None,
                "social_boost": social_boost if social_boost > 0 else None,
                "social_buzz":  social_summary if social_boost > 0 else None,
            }

    scores = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(_score_moonshot, sym): sym for sym in all_candidates}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result:
                    scores.append(result)
            except Exception as e:
                log.debug(f"[MOONSHOT] Score failed for {futures[f]}: {e}")

    if not scores:
        scanner_log("🌙 [MOONSHOT] No qualifying candidates.")
        return None

    scores.sort(key=lambda x: x["score"]
                + (5  if x.get("_is_new")      else 0)
                + (8  if x.get("_is_trending")  else 0),
                reverse=True)
    best = scores[0]
    last_top_alt = best
    trend_tag = "🔥" if best.get("_is_trending") else ("🆕" if best.get("_is_new") else "")
    scanner_log(f"🌙 [MOONSHOT] Top: {best['symbol']}{trend_tag} | "
                f"Score: {best['score']}/100 | 1h: {best['_1h_chg']:+.1f}% | RSI: {best['rsi']}"
                + (f" | 🔥 {best['_trend_reason']}" if best.get("_trend_reason") else ""))

    # Burst detection — tightened: single threshold of MOONSHOT_MIN_VOL_BURST for both types
    tradeable = []
    for s in scores:
        df_k   = s.pop("_df", None)
        is_new = s.pop("_is_new", False)
        s.pop("_1h_chg",      None)
        s.pop("_is_trending", None)
        s.pop("_trend_reason",None)

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

    close  = df5m["close"]
    opens  = df5m["open"]
    volume = df5m["volume"]
    lows   = df5m["low"]

    # ── RSI oversold filter ───────────────────────────────────
    rsi = calc_rsi(close)
    if np.isnan(rsi) or rsi > REVERSAL_MAX_RSI:
        return None

    # ── Capitulation candle check (prior candle) ──────────────
    # Must be a significant red candle with elevated volume (the sell climax)
    cap_open  = float(opens.iloc[-2])
    cap_close = float(close.iloc[-2])
    cap_low   = float(lows.iloc[-2])
    cap_vol   = float(volume.iloc[-2])
    avg_vol   = float(volume.iloc[-22:-2].mean())  # 20-candle avg excluding cap + bounce

    if cap_close >= cap_open:
        return None  # prior candle must be red (the capitulation)

    if avg_vol > 0 and cap_vol < avg_vol * 1.5:
        return None  # capitulation candle needs elevated volume

    cap_body = cap_open - cap_close  # size of the red candle body

    # ── Bounce candle check (current candle) ──────────────────
    curr_open  = float(opens.iloc[-1])
    curr_close = float(close.iloc[-1])
    curr_vol   = float(volume.iloc[-1])

    if curr_close <= curr_open:
        return None  # current candle must be green (the bounce started)

    # Must reclaim ≥ REVERSAL_BOUNCE_RECOVERY of the cap candle body
    recovery = (curr_close - curr_open) / cap_body if cap_body > 0 else 0
    if recovery < REVERSAL_BOUNCE_RECOVERY:
        return None  # weak bounce — hasn't reclaimed enough ground

    # Bounce volume must show buyers stepping in (≥ 1.2× avg)
    # This distinguishes real bounces from dead-cat ticks
    if avg_vol > 0 and curr_vol < avg_vol * REVERSAL_VOL_RECOVERY:
        return None  # low bounce volume — not convincing

    # ── Cap-candle SL anchor ──────────────────────────────────
    # SL goes just below the capitulation candle's low — that's where
    # the reversal thesis definitively breaks. Store as pct from current price.
    entry_est   = curr_close
    cap_sl_pct  = max(
        REVERSAL_SL,
        (entry_est - cap_low) / entry_est + REVERSAL_CAP_SL_BUFFER
    )
    cap_sl_pct  = min(cap_sl_pct, 0.05)  # never risk more than 5% on a reversal

    return {
        "symbol":      sym,
        "price":       entry_est,
        "rsi":         round(rsi, 2),
        "score":       round(rsi, 2),
        "recovery":    round(recovery, 3),    # how much of cap body was reclaimed
        "cap_vol_ratio": round(cap_vol / avg_vol, 2) if avg_vol > 0 else 1.0,
        "bounce_vol_ratio": round(curr_vol / avg_vol, 2) if avg_vol > 0 else 1.0,
        "cap_sl_pct":  round(cap_sl_pct, 4), # SL anchored below cap-candle low
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
            try:
                result = f.result()
                if result:
                    tradeable.append(result)
            except Exception as e:
                log.debug(f"[REVERSAL] Score failed for {futures[f]}: {e}")

    if not tradeable:
        scanner_log("🔄 [REVERSAL] No oversold pairs with capitulation + green candle.")
        return None

    tradeable.sort(key=lambda x: x["rsi"])
    best = tradeable[0]
    last_top_alt = best
    scanner_log(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | "
                f"Recovery: {best.get('recovery',0)*100:.0f}% | "
                f"BounceVol: {best.get('bounce_vol_ratio',0):.1f}× | "
                f"SL: -{best.get('cap_sl_pct',REVERSAL_SL)*100:.1f}%")

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
        telegram(f"⚠️ <b>TP limit order failed</b> [{label}]\n"
                 f"{symbol} qty={qty} @ {price}\n{str(body)[:200]}\n"
                 f"Bot will monitor TP by price polling instead.")
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


def get_actual_fills(symbol: str, since_ms: int, retries: int = 3,
                     buy_order_id=None, sell_order_ids: set | None = None) -> dict:
    """
    Fetch actual fill data from MEXC myTrades for a symbol since a timestamp.

    When buy_order_id is provided, buy fills are filtered to that order only.
    When sell_order_ids is provided, sell fills are filtered to those orders only.
    If neither is provided (legacy fallback), sell qty is capped at buy qty to
    prevent double-counting when both TP limit and SL market sell fire together.

    Retries up to `retries` times with 1s delay to allow fills to settle.
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

            all_buys  = [f for f in fills if     f.get("isBuyer")]
            all_sells = [f for f in fills if not f.get("isBuyer")]

            # ── Filter by order ID when available (most precise) ──
            if buy_order_id:
                buys = [f for f in all_buys if str(f.get("orderId")) == str(buy_order_id)]
                if not buys:
                    buys = all_buys  # fall back if orderId not in response
            else:
                buys = all_buys

            if sell_order_ids:
                sells = [f for f in all_sells if str(f.get("orderId")) in
                         {str(s) for s in sell_order_ids}]
                if not sells:
                    sells = all_sells  # fall back if orderId not in response
            else:
                sells = all_sells

            # ── Qty cap safety net ────────────────────────────────
            # Even with order ID filtering, cap sell qty at buy qty to prevent
            # double-counting from any race condition (TP limit + SL market sell).
            qty_bought = sum(float(f["qty"]) for f in buys)
            if qty_bought > 0:
                qty_sold_acc = 0.0
                capped_sells = []
                for sell in sorted(sells, key=lambda f: int(f.get("time", 0))):
                    qty_this = float(sell["qty"])
                    if qty_sold_acc + qty_this <= qty_bought * FILL_QTY_TOLERANCE:
                        capped_sells.append(sell)
                        qty_sold_acc += qty_this
                    else:
                        log.warning(f"[FILLS] {symbol}: capped extra sell fill "
                                    f"(qty {qty_this:.4f}, already sold {qty_sold_acc:.4f} "
                                    f"of {qty_bought:.4f} bought) — likely TP+SL race condition")
                sells = capped_sells

            # Fees — MEXC pays in the received asset, convert to USDT
            fee_usdt = 0.0
            for f in buys + sells:
                commission = float(f.get("commission", 0))
                asset      = f.get("commissionAsset", "")
                if asset == "USDT":
                    fee_usdt += commission
                elif commission > 0:
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

            if result["avg_buy_price"] is not None:
                return result

        except Exception as e:
            log.debug(f"myTrades fetch failed {symbol}: {e}")

        if attempt < retries - 1:
            time.sleep(1)

    return {}

# ── Dynamic TP / SL calculator ────────────────────────────────

def calc_dynamic_tp_sl(opp: dict) -> tuple[float, float, str, str]:
    """
    Calculate signal-aware TP and SL percentages for a SCALPER trade.

    Uses three entry-signal dimensions from the candidate dict:
      crossed_now    — fresh EMA9/21 crossover (most potent signal)
      vol_ratio      — volume spike size
      rsi            — RSI at entry (lower = more oversold = mean-reversion)
      score          — overall confidence (multi-signal = more room)
      ema21_dist_pct — EMA21 distance as SL anchor for crossover entries
      avg_candle_pct — recent average candle body (reality cap for TP, noise
                       floor for SL)

    Returns (tp_pct, sl_pct, tp_label, sl_label) where labels describe
    what drove each level — shown in the open trade Telegram message.
    """
    atr_pct        = opp.get("atr_pct",        0.015)
    vol_ratio      = opp.get("vol_ratio",       1.0)
    rsi            = opp.get("rsi",             50.0)
    score          = opp.get("score",           0.0)
    crossed_now    = opp.get("crossed_now",     False)
    ema21_dist_pct = opp.get("ema21_dist_pct",  atr_pct * SCALPER_ATR_MULT)
    avg_candle_pct = opp.get("avg_candle_pct",  atr_pct)

    # ── TP ─────────────────────────────────────────────────────
    if crossed_now:
        tp_mult  = SCALPER_TP_MULT_CROSSOVER
        tp_label = f"crossover×{tp_mult}"
    elif vol_ratio >= 3.0:
        tp_mult  = SCALPER_TP_MULT_VOL_SPIKE
        tp_label = f"vol×{tp_mult}"
    elif rsi < 40:
        tp_mult  = SCALPER_TP_MULT_OVERSOLD
        tp_label = f"oversold×{tp_mult}"
    else:
        tp_mult  = SCALPER_TP_MULT_DEFAULT
        tp_label = f"trend×{tp_mult}"

    atr_tp      = atr_pct * tp_mult
    candle_cap  = avg_candle_pct * SCALPER_TP_CANDLE_MULT
    tp_pct      = min(atr_tp, candle_cap)             # whichever is more conservative
    tp_pct      = min(SCALPER_TP_MAX, max(SCALPER_TP_MIN, tp_pct))

    if atr_tp > candle_cap:
        tp_label += f" (candle-capped {candle_cap*100:.1f}%)"

    # ── SL ─────────────────────────────────────────────────────
    if vol_ratio >= 3.0:
        sl_mult  = SCALPER_SL_MULT_VOL_SPIKE
        sl_label = f"tight×{sl_mult} (vol spike)"
    elif rsi < 40:
        sl_mult  = SCALPER_SL_MULT_OVERSOLD
        sl_label = f"tight×{sl_mult} (oversold)"
    elif score >= SCALPER_BREAKEVEN_SCORE:
        sl_mult  = SCALPER_SL_MULT_HIGH_CONF
        sl_label = f"wide×{sl_mult} (high confidence)"
    else:
        sl_mult  = SCALPER_SL_MULT_DEFAULT
        sl_label = f"standard×{sl_mult}"

    atr_sl      = atr_pct * sl_mult

    # For crossover entries, anchor SL to EMA21 distance — that's where
    # the thesis actually breaks. Use whichever is larger (EMA21 or ATR-based)
    # to avoid placing SL inside normal price oscillation.
    if crossed_now and ema21_dist_pct > 0:
        sl_pct   = max(atr_sl, ema21_dist_pct)
        sl_label = f"EMA21 anchor ({ema21_dist_pct*100:.2f}%)"
    else:
        sl_pct   = atr_sl

    # Noise floor — SL must be ≥ N average candle bodies wide
    noise_floor = avg_candle_pct * SCALPER_SL_NOISE_MULT
    if sl_pct < noise_floor:
        sl_pct   = noise_floor
        sl_label += f" (noise-floored {noise_floor*100:.2f}%)"

    sl_pct = min(SCALPER_SL_MAX, max(SCALPER_SL_MIN, sl_pct))

    log.info(f"[SCALPER] Dynamic TP: {tp_pct*100:.2f}% [{tp_label}] | "
             f"SL: {sl_pct*100:.2f}% [{sl_label}] | "
             f"R:R {tp_pct/sl_pct:.1f}:1")

    return tp_pct, sl_pct, tp_label, sl_label


# ── Trade lifecycle ────────────────────────────────────────────

def calc_risk_budget(opp: dict, balance: float) -> tuple[float, float, float, str, str]:
    """
    Risk-based position sizing for SCALPER.
    Computes TP/SL via calc_dynamic_tp_sl once, then derives the budget so
    hitting the SL costs exactly SCALPER_RISK_PER_TRADE of current balance.

      budget = (balance × RISK_PCT) / sl_pct

    Hard-capped at SCALPER_BUDGET_PCT to prevent oversized positions on tiny SLs.
    Returns (budget, tp_pct, sl_pct, tp_label, sl_label) so the caller can pass
    the pre-computed TP/SL directly into open_position — avoiding a second call.
    Falls back to the percentage cap if dynamic TP/SL can't be computed.
    """
    try:
        tp_pct, sl_pct, tp_label, sl_label = calc_dynamic_tp_sl(opp)
        if sl_pct > 0:
            risk_budget = (balance * SCALPER_RISK_PER_TRADE) / sl_pct
            capped      = min(risk_budget, balance * SCALPER_BUDGET_PCT)
            return round(capped, 2), tp_pct, sl_pct, tp_label, sl_label
    except Exception:
        pass
    # Fallback — use pct cap and let open_position compute TP/SL itself
    return round(balance * SCALPER_BUDGET_PCT, 2), 0.0, 0.0, "", ""


def open_position(opp, budget_usdt, tp_pct, sl_pct, label, max_hours=None):
    symbol                              = opp["symbol"]

    # Last-moment duplicate guard — belt-and-suspenders check before any order is placed.
    # open_symbols filtering in find_scalper_opportunity handles the normal case;
    # this catches the rare window where two paths converge on the same symbol.
    if any(t["symbol"] == symbol for t in scalper_trades + alt_trades):
        log.warning(f"[{label}] Duplicate guard: {symbol} already in open positions — skipping")
        return None

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

    # 🟢 Spread / depth check — reject pairs with wide bid/ask before money moves.
    # SCALPER: tight 0.4% threshold — small TP, spread eats the profit.
    # MOONSHOT: wider 0.8% threshold — larger TP absorbs more, but still filter thin markets.
    # Check is advisory — never blocks on error.
    spread_limit = SCALPER_MAX_SPREAD if label == "SCALPER" else MOONSHOT_MAX_SPREAD
    if label in ("SCALPER", "MOONSHOT") and not PAPER_TRADE:
        try:
            depth    = public_get("/api/v3/depth", {"symbol": symbol, "limit": 5})
            bids     = depth.get("bids", [])
            asks     = depth.get("asks", [])
            if bids and asks:
                best_bid = float(bids[0][0])
                best_ask = float(asks[0][0])
                mid      = (best_bid + best_ask) / 2
                spread   = (best_ask - best_bid) / mid if mid > 0 else 1.0
                if spread > spread_limit:
                    log.info(f"[{label}] Skip {symbol} — spread {spread*100:.3f}% "
                             f"> {spread_limit*100:.1f}%")
                    return None
        except Exception:
            pass  # spread check is advisory — don't block on error

    buy_order = place_market_buy(symbol, qty, label)
    if not buy_order:
        return None
    buy_order_id = buy_order.get("orderId")  # stored for precise fill filtering

    # Fetch actual fill price — more accurate than the pre-order ticker price
    actual_fills = get_actual_fills(symbol, since_ms=bought_at_ms,
                                    buy_order_id=buy_order_id)
    actual_entry = actual_fills.get("avg_buy_price") or price
    actual_cost  = actual_fills.get("cost_usdt")     or notional
    if actual_fills.get("avg_buy_price"):
        log.info(f"[{label}] Actual fill: ${actual_entry:.6f} "
                 f"(ticker was ${price:.6f}, slippage: {(actual_entry/price-1)*100:+.3f}%)")
    else:
        log.info(f"[{label}] Using ticker price (myTrades unavailable): ${price:.6f}")

    # SCALPER: dynamic signal-aware TP and SL.
    # If pre-computed values are passed in (tp_pct > 0), use them directly —
    # calc_risk_budget already ran calc_dynamic_tp_sl to derive the budget.
    # Falls back to calling calc_dynamic_tp_sl if no pre-computed values exist.
    # REVERSAL: SL anchored to cap-candle low stored in opp["cap_sl_pct"]
    # MOONSHOT: fixed pct TP/SL passed in from caller
    if label == "SCALPER" and opp.get("atr_pct"):
        if tp_pct > 0 and sl_pct > 0:
            used_tp_pct = tp_pct
            actual_sl   = sl_pct
            tp_label    = ""
            sl_label    = ""
        else:
            used_tp_pct, actual_sl, tp_label, sl_label = calc_dynamic_tp_sl(opp)
        tp_price = round_price_to_tick(actual_entry * (1 + used_tp_pct), tick_size)
    elif label == "REVERSAL" and opp.get("cap_sl_pct"):
        used_tp_pct = tp_pct
        actual_sl   = opp["cap_sl_pct"]   # cap-candle anchored SL
        tp_label    = ""
        sl_label    = f"cap-candle anchor (-{actual_sl*100:.1f}%)"
        tp_price    = round_price_to_tick(actual_entry * (1 + tp_pct), tick_size)
    else:
        # MOONSHOT: fixed pct TP/SL passed in from caller
        used_tp_pct = tp_pct
        actual_sl   = sl_pct
        tp_label    = ""
        sl_label    = ""
        tp_price    = round_price_to_tick(actual_entry * (1 + tp_pct), tick_size)

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
        "buy_order_id":   buy_order_id,   # used to filter fills precisely in close_position
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
        "sentiment":      opp.get("sentiment"),
        # ATR-based trail width — set at entry from scorer, persisted across restarts.
        # check_exit uses this instead of the static SCALPER_TRAIL_PCT constant.
        "trail_pct":      opp.get("trail_pct", SCALPER_TRAIL_PCT) if label == "SCALPER" else None,
        # High-confidence scalper trades get fast breakeven: SL moves to entry at +1.5%
        # Moonshot trades get breakeven at +4% — prevents giving back gains before partial TP
        "breakeven_act":  (SCALPER_BREAKEVEN_ACT if (
                               label == "SCALPER" and
                               opp.get("score", 0) >= SCALPER_BREAKEVEN_SCORE
                           ) else MOONSHOT_BREAKEVEN_ACT if label == "MOONSHOT"
                           else None),
        "breakeven_done": False,   # flips True once SL has been moved to entry
        # ── Partial TP (MOONSHOT / REVERSAL only) ─────────────
        # Stage 1: sell partial_tp_ratio of qty at partial_tp_price.
        # After stage 1: sl_price moves to entry (remainder is risk-free),
        # qty and budget_used updated to reflect remaining position.
        "partial_tp_price": (
            round_price_to_tick(actual_entry * (1 + MOONSHOT_PARTIAL_TP_PCT), tick_size)
            if label == "MOONSHOT" else
            round_price_to_tick(actual_entry * (1 + REVERSAL_PARTIAL_TP_PCT), tick_size)
            if label == "REVERSAL" else None
        ),
        "partial_tp_ratio": (
            MOONSHOT_PARTIAL_TP_RATIO if label == "MOONSHOT" else
            REVERSAL_PARTIAL_TP_RATIO if label == "REVERSAL" else None
        ),
        "partial_tp_hit":   False,   # flips True once stage 1 fires
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
        sentiment_icon = "🟢" if sentiment_val > 0 else "🔴"
        sentiment_line = f"Sentiment:   {sentiment_icon} {sentiment_val:+.1f}pts\n"

    social_buzz = opp.get("social_buzz")
    social_line = f"Social:      🔥 +{opp['social_boost']:.0f}pts — {social_buzz}\n" \
                  if social_buzz else ""

    if label == "SCALPER" and tp_label:
        tp_display = (f"Take profit: <b>${tp_price:.6f}</b>  (+{used_tp_pct*100:.1f}%)"
                      f"  <i>[{tp_label}]</i>\n")
        sl_display = (f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl*100:.1f}%)"
                      f"  <i>[{sl_label}]</i> [market]\n")
    elif label == "REVERSAL" and sl_label:
        tp_display = f"Take profit: <b>${tp_price:.6f}</b>  (+{used_tp_pct*100:.0f}%)\n"
        sl_display = (f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl*100:.1f}%)"
                      f"  <i>[{sl_label}]</i> [market]\n")
    else:
        tp_display = f"Take profit: <b>${tp_price:.6f}</b>  (+{used_tp_pct*100:.0f}%)\n"
        sl_display = f"Stop loss:   <b>${sl_price:.6f}</b>  (-{actual_sl*100:.1f}%) [market]\n"

    partial_tp_line = ""
    if trade.get("partial_tp_price") and label == "MOONSHOT":
        ratio_pct   = (trade["partial_tp_ratio"] or 0.5) * 100
        partial_pct = (trade["partial_tp_price"] / actual_entry - 1) * 100
        partial_tp_line = (f"Partial TP:  {ratio_pct:.0f}% @ "
                           f"<b>${trade['partial_tp_price']:.6f}</b>"
                           f"  (+{partial_pct:.1f}%) → trail {MOONSHOT_TRAIL_PCT*100:.0f}% stop\n")
    elif trade.get("partial_tp_price") and label == "REVERSAL":
        ratio_pct   = (trade["partial_tp_ratio"] or 0.5) * 100
        partial_pct = (trade["partial_tp_price"] / actual_entry - 1) * 100
        partial_tp_line = (f"Partial TP:  {ratio_pct:.0f}% @ "
                           f"<b>${trade['partial_tp_price']:.6f}</b>"
                           f"  (+{partial_pct:.1f}%) → SL → entry\n")

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
        f"{social_line}"
        f"{tp_display}"
        f"{sl_display}"
        f"{partial_tp_line}"
        f"{breakeven_line}"
        f"{timeout_line}"
        f"{tp_status}\n"
        f"Score: {opp.get('score',0)}"
        + (f" 🔥 (confluence +{opp.get('confluence_bonus',0):.0f})" if opp.get('confluence_bonus') else "")
        + f" | RSI: {opp.get('rsi','?')} ({opp.get('rsi_delta',0):+.1f}) | Vol: {opp.get('vol_ratio','?')}x"
        + (f" | Trail: {opp.get('trail_pct', SCALPER_TRAIL_PCT)*100:.1f}%" if label == "SCALPER" else "")
    )
    save_state()
    return trade


def check_exit(trade, best_score: float = 0) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")

    # held_min computed once here — used by timeout checks, graduated exits,
    # flat exit, vol collapse, and trailing stop logic below.
    held_min = (datetime.now(timezone.utc) -
                datetime.fromisoformat(trade["opened_at"])).total_seconds() / 60

    # ── Timeout logic ─────────────────────────────────────────
    # MOONSHOT: graduated — timeout depends on how the trade is performing.
    #   Flat trade gets cut early; a trade that's working gets more time.
    # REVERSAL: hard 2h ceiling (short-hold strategy, no accommodation).
    # SCALPER: no max_hours (uses trailing stop / flat exit instead).
    if trade.get("max_hours"):
        if label == "MOONSHOT":
            # Once partial TP has fired the trade is risk-free — let the trailing
            # stop run it. Only apply the hard timeout to trades still in stage 1.
            if not trade.get("partial_tp_hit") and held_min >= MOONSHOT_TIMEOUT_MAX_MINS:
                log.info(f"⏰ [{label}] Max timeout ({MOONSHOT_TIMEOUT_MAX_MINS}min): {symbol}")
                return True, "TIMEOUT"
        else:
            if held_min / 60 >= trade["max_hours"]:
                log.info(f"⏰ [{label}] Timeout: {symbol}")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TIMEOUT"

    # Use live WS price when available — avoids a REST call per trade per cycle.
    # Falls back to REST if WS not yet connected, stale, or symbol not subscribed.
    price = ws_price(symbol)
    if price is None:
        try:
            price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
        except Exception as e:
            log.error(f"Price fetch error {symbol}: {e}")
            return False, ""

    pct = (price - trade["entry_price"]) / trade["entry_price"] * 100
    trade["highest_price"] = max(trade.get("highest_price", price), price)

    # Hard safety SL — fires 4% below the trade's actual SL as a backstop.
    # Hardcoding -5% was wrong for MOONSHOT (SL is now -8%): it would have
    # triggered before the real SL, overriding it on normal volatility.
    hard_sl_pct = -(trade.get("sl_pct", 0.05) * 100 + 4.0)
    if pct <= hard_sl_pct:
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

    # ── Partial TP (MOONSHOT / REVERSAL) ──────────────────────
    # Stage 1: fire when price hits partial_tp_price and stage hasn't fired yet.
    # After this, execute_partial_tp() sells half, moves SL to entry, trade continues.
    if (label in ("MOONSHOT", "REVERSAL")
            and not trade.get("partial_tp_hit")
            and trade.get("partial_tp_price")
            and price >= trade["partial_tp_price"]):
        log.info(f"🎯½ [{label}] Partial TP: {symbol} | {pct:+.2f}%")
        return True, "PARTIAL_TP"

    # ── TP exit logic ─────────────────────────────────────────
    # SCALPER: check if exchange limit order was filled
    # MOONSHOT after partial TP: trailing stop — uncapped upside, ride the wave
    # MOONSHOT before partial TP / REVERSAL: price polling against fixed tp_price
    if label == "SCALPER":
        if not PAPER_TRADE and tp_order_id:
            if tp_order_id not in get_open_order_ids(symbol):
                if price >= trade["tp_price"] * 0.995:
                    log.info(f"🎯 [{label}] TP limit filled: {symbol}")
                    return True, "TAKE_PROFIT"
                else:
                    log.warning(f"⚠️ [{label}] TP order vanished but price ${price:.6f} "
                                f"never reached TP ${trade['tp_price']:.6f} — "
                                f"order was cancelled not filled. Monitoring manually.")
                    trade["tp_order_id"] = None
        if PAPER_TRADE or not tp_order_id:
            if price >= trade["tp_price"]:
                log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
                return True, "TAKE_PROFIT"

    elif label == "MOONSHOT" and trade.get("partial_tp_hit"):
        # After partial TP: trailing stop on remainder — no fixed target, ride the move.
        # Trails MOONSHOT_TRAIL_PCT below highest price seen since entry.
        trail_sl = trade["highest_price"] * (1 - MOONSHOT_TRAIL_PCT)
        if price <= trail_sl:
            log.info(f"📉 [{label}] Trail stop: {symbol} | {pct:+.2f}% | "
                     f"high {((trade['highest_price']/trade['entry_price'])-1)*100:.1f}%")
            return True, "TRAILING_STOP"

    else:
        # MOONSHOT (pre-partial) / REVERSAL: fixed TP price check
        if price >= trade["tp_price"]:
            log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
            return True, "TAKE_PROFIT"

    # ── MOONSHOT-specific exits ───────────────────────────────
    if label == "MOONSHOT":
        # Graduated timeout — give winning trades more time
        if pct < 0.5 and held_min >= MOONSHOT_TIMEOUT_FLAT_MINS:
            log.info(f"😴 [{label}] Flat timeout: {symbol} | {pct:+.2f}% after {held_min:.0f}min")
            return True, "TIMEOUT"
        if pct < 5.0 and held_min >= MOONSHOT_TIMEOUT_MARGINAL_MINS:
            log.info(f"⏰ [{label}] Marginal timeout: {symbol} | {pct:+.2f}% after {held_min:.0f}min")
            return True, "TIMEOUT"

        # Mid-hold volume collapse — pump is over if volume has dried up
        # Only check after MOONSHOT_VOL_CHECK_MINS to avoid noise on entry
        if held_min >= MOONSHOT_VOL_CHECK_MINS and pct < 5.0:
            try:
                df_vol = parse_klines(symbol, interval="5m", limit=25, min_len=10)
                if df_vol is not None:
                    vol       = df_vol["volume"]
                    avg_vol   = float(vol.iloc[-21:-1].mean())
                    curr_vol  = float(vol.iloc[-1])
                    vol_ratio = (curr_vol / avg_vol) if avg_vol > 0 else 1.0
                    if vol_ratio < MOONSHOT_VOL_COLLAPSE_RATIO:
                        log.info(f"📉 [{label}] Vol collapse: {symbol} | "
                                 f"vol {vol_ratio:.2f}× avg | {pct:+.2f}%")
                        return True, "VOL_COLLAPSE"
            except Exception:
                pass  # never block an exit check on a kline failure

    # ── Breakeven lock (any label with breakeven_act set) ────────
    # Fires once when trade reaches breakeven_act — moves SL to entry.
    # Scalper: high-confidence trades at +1.5%. Moonshot: all trades at +4%.
    breakeven_act = trade.get("breakeven_act")
    if breakeven_act and not trade.get("breakeven_done") and pct >= breakeven_act * 100:
        if trade["sl_price"] < trade["entry_price"]:
            trade["sl_price"]       = trade["entry_price"]
            trade["breakeven_done"] = True
            log.info(f"🔒 [{label}] Breakeven locked: {symbol} | {pct:+.2f}% | "
                     f"SL moved to entry ${trade['entry_price']:.6f}")

    if label == "SCALPER":
        # ── Trailing stop ─────────────────────────────────────────
        # trail_pct is computed at entry from ATR — wider on volatile coins,
        # tighter on calm ones. Falls back to static constant for old trades.
        trail_pct = trade.get("trail_pct") or SCALPER_TRAIL_PCT
        if trade["highest_price"] >= trade["entry_price"] * (1 + SCALPER_TRAIL_ACT):
            if price <= trade["highest_price"] * (1 - trail_pct):
                log.info(f"📉 [{label}] Trailing stop: {symbol} | {pct:+.2f}% "
                         f"(trail {trail_pct*100:.1f}%)")
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


def execute_partial_tp(trade) -> bool:
    """
    Sell partial_tp_ratio of the position at market price (stage 1 TP).
    Mutates the trade dict in place — the trade stays live with reduced qty.

    After firing:
      - partial_tp_hit  = True
      - qty             = remaining qty after partial sell
      - budget_used     = proportional remaining cost basis
      - sl_price        = entry_price (remainder is now risk-free)
      - A partial P&L entry is appended to trade_history

    Returns True if partial sell succeeded, False if it failed hard.
    """
    label   = trade["label"]
    symbol  = trade["symbol"]
    ratio   = trade.get("partial_tp_ratio", 0.5)

    min_qty, step_size, _, _ = get_symbol_rules(symbol)
    full_qty = trade["qty"]

    # Use Decimal to avoid float representation errors (same approach as calc_qty)
    d_full  = Decimal(str(full_qty))
    d_ratio = Decimal(str(ratio))
    d_step  = Decimal(str(step_size))
    partial_qty   = float((d_full * d_ratio / d_step).to_integral_value(rounding=ROUND_DOWN) * d_step)
    # Floor remaining to step_size as well — prevents lot-size errors on micro-priced coins
    remaining_qty = float(((d_full - Decimal(str(partial_qty))) / d_step)
                          .to_integral_value(rounding=ROUND_DOWN) * d_step)

    # Safety: don't fire if either partial or remaining qty would be below min
    if partial_qty < min_qty or remaining_qty < min_qty:
        log.warning(f"[{label}] Partial TP skipped — qty too small "
                    f"(partial={partial_qty}, remaining={remaining_qty}, min={min_qty})")
        # Skip partial, just let the full TP run
        trade["partial_tp_hit"] = True   # mark as hit so we don't retry
        return True

    partial_sell_id  = None
    partial_sold_at_ms = int(time.time() * 1000)  # record before sell for fill query
    if not PAPER_TRADE:
        try:
            result = private_post("/api/v3/order", {
                "symbol": symbol, "side": "SELL",
                "type": "MARKET", "quantity": str(partial_qty),
            })
            partial_sell_id = result.get("orderId")
            log.info(f"✅ [{label}] Partial sell: {partial_qty} {symbol} → {result}")
        except requests.exceptions.HTTPError as e:
            try:    body = e.response.json()
            except: body = {"msg": str(e)}
            log.error(f"🚨 [{label}] Partial sell failed: {body}")
            telegram(f"🚨 <b>Partial TP sell failed!</b> [{label}] {symbol}\n"
                     f"{str(body)[:200]}\nClose manually if needed.")
            return False

    # Fetch partial fill for accurate P&L
    # Use partial_sold_at_ms (not original bought_at_ms) so we only see the partial sell
    partial_fills = {}
    if not PAPER_TRADE:
        sell_ids = {partial_sell_id} if partial_sell_id else None
        partial_fills = get_actual_fills(
            symbol, since_ms=partial_sold_at_ms, retries=3,
            buy_order_id=None,          # not filtering buys — we want sell only
            sell_order_ids=sell_ids,
        )

    try:
        ticker_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except:
        ticker_price = trade["partial_tp_price"]

    actual_entry = partial_fills.get("avg_buy_price")  or trade["entry_price"]
    actual_exit  = partial_fills.get("avg_sell_price") or ticker_price
    fee_usdt     = partial_fills.get("fee_usdt", 0.0)

    # Cost basis for partial: proportional share of the full position cost
    partial_cost = round(trade["budget_used"] * ratio, 4)
    partial_rev  = round(actual_exit * partial_qty, 4)
    partial_pnl  = round(partial_rev - partial_cost - fee_usdt, 4)
    partial_pct  = round(partial_pnl / partial_cost * 100, 4) if partial_cost > 0 else 0.0

    # Record partial close in trade_history as its own entry
    trade_history.append({
        **{k: v for k, v in trade.items() if not k.startswith("_")},
        "qty":           partial_qty,
        "budget_used":   partial_cost,
        "exit_price":    actual_exit,
        "exit_ticker":   ticker_price,
        "exit_reason":   "PARTIAL_TP",
        "closed_at":     datetime.now(timezone.utc).isoformat(),
        "fee_usdt":      fee_usdt,
        "cost_usdt":     partial_cost,
        "revenue_usdt":  partial_rev,
        "pnl_pct":       partial_pct,
        "pnl_usdt":      partial_pnl,
        "fills_used":    bool(partial_fills.get("avg_sell_price")),
        "is_partial":    True,
    })

    # Mutate trade dict — position continues with reduced qty
    trade["qty"]               = remaining_qty
    trade["budget_used"]       = round(trade["budget_used"] * (1 - ratio), 4)
    trade["sl_price"]          = trade["entry_price"]   # remainder is now risk-free
    trade["partial_tp_hit"]    = True
    # close_position uses this as bought_at_ms so fill query only sees remaining fills
    trade["bought_at_ms"]      = partial_sold_at_ms

    # Save immediately after mutation — minimises the crash window between
    # "sell confirmed on exchange" and "state reflects reduced position"
    save_state()

    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    fills_note= "✅ actual fills" if partial_fills.get("avg_sell_price") else "⚠️ estimated"
    icon      = {"MOONSHOT":"🌙","REVERSAL":"🔄"}.get(label, "🎯")

    log.info(f"🎯½ [{label}] Partial TP {symbol}: sold {partial_qty} @ ${actual_exit:.6f} "
             f"P&L ${partial_pnl:+.4f} ({partial_pct:+.2f}%) | "
             f"Remaining: {remaining_qty} @ SL entry")
    telegram(
        f"🎯½ <b>Partial TP — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:      <b>{symbol}</b>\n"
        f"Sold:      {partial_qty} ({ratio*100:.0f}%) @ <b>${actual_exit:.6f}</b>  [{fills_note}]\n"
        f"P&L:       <b>{partial_pct:+.2f}%  (${partial_pnl:+.2f})</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Remaining: {remaining_qty} still open\n"
        f"SL moved:  entry ${trade['entry_price']:.6f} (risk-free 🔒)\n"
        + (f"Trail:     {MOONSHOT_TRAIL_PCT*100:.0f}% below highest price (uncapped)"
           if label == "MOONSHOT" else
           f"Target:    ${trade['tp_price']:.6f}  (+{trade['tp_pct']*100:.0f}%)")
    )
    return True


def close_position(trade, reason) -> bool:
    label  = trade["label"]
    symbol = trade["symbol"]

    # For MOONSHOT/REVERSAL: market sell on ALL exits including TAKE_PROFIT
    # (no exchange limit order was placed, so we always need to sell manually)
    # For SCALPER: TAKE_PROFIT is handled by exchange limit, others need market sell
    needs_sell = (
        (label in ("MOONSHOT", "REVERSAL")) or
        (label == "SCALPER" and reason in ("STOP_LOSS","TRAILING_STOP","TIMEOUT","FLAT_EXIT","ROTATION","VOL_COLLAPSE"))
    )

    sell_order_id = None
    if needs_sell and not PAPER_TRADE:
        # For SCALPER: if there's a live TP limit order, cancel it and verify
        # it's gone before placing the market sell. Without this, the market sell
        # can fail with "insufficient balance" because funds are still locked in
        # the open TP order (MEXC processes cancels asynchronously).
        tp_order_id = trade.get("tp_order_id")
        if label == "SCALPER" and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
            # Brief poll to confirm cancel — up to 3 checks × 0.3s = 0.9s max wait
            for _ in range(3):
                time.sleep(0.3)
                if tp_order_id not in get_open_order_ids(symbol):
                    break
            # Clear from trade dict regardless — even if poll timed out,
            # the cancel request was sent and we proceed with market sell
            trade["tp_order_id"] = None

        try:
            result = private_post("/api/v3/order", {
                "symbol": symbol, "side": "SELL",
                "type": "MARKET", "quantity": str(trade["qty"])
            })
            sell_order_id = result.get("orderId")
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
        bought_at_ms  = trade.get("bought_at_ms", int(time.time() * 1000) - 86400_000)
        buy_order_id  = trade.get("buy_order_id")
        # Collect all sell order IDs we know about (TP limit + any market sell)
        known_sell_ids = set()
        if trade.get("tp_order_id"):
            known_sell_ids.add(trade["tp_order_id"])
        if sell_order_id:
            known_sell_ids.add(sell_order_id)

        retries    = 5 if (reason == "TAKE_PROFIT" and label == "SCALPER") else 3
        exit_fills = get_actual_fills(
            symbol, since_ms=bought_at_ms, retries=retries,
            buy_order_id=buy_order_id,
            sell_order_ids=known_sell_ids or None,
        )

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

    # Track consecutive scalper losses for the streak circuit breaker
    global _consecutive_losses, _win_rate_pause_until
    if label == "SCALPER":
        if pnl_pct <= 0:
            _consecutive_losses += 1
        else:
            _consecutive_losses = 0   # any win resets the streak

    # Win-rate circuit breaker — check after every full (non-partial) close.
    # Only counts SCALPER trades since the CB only blocks scalper entries.
    # If the last WIN_RATE_CB_WINDOW scalper trades have win rate below threshold → 1h pause.
    full_recent = [t for t in trade_history
                   if not t.get("is_partial")
                   and t.get("label") == "SCALPER"][-WIN_RATE_CB_WINDOW:]
    if len(full_recent) >= WIN_RATE_CB_WINDOW:
        recent_win_rate = sum(1 for t in full_recent if t["pnl_pct"] > 0) / WIN_RATE_CB_WINDOW
        if recent_win_rate < WIN_RATE_CB_THRESHOLD and time.time() >= _win_rate_pause_until:
            _win_rate_pause_until = time.time() + WIN_RATE_CB_PAUSE_MINS * 60
            log.warning(f"🛑 Win-rate CB: {recent_win_rate*100:.0f}% over last "
                        f"{WIN_RATE_CB_WINDOW} trades — pausing {WIN_RATE_CB_PAUSE_MINS}min")
            telegram(
                f"🛑 <b>Win-rate circuit breaker triggered</b>\n"
                f"Win rate: <b>{recent_win_rate*100:.0f}%</b> over last {WIN_RATE_CB_WINDOW} trades "
                f"(threshold: {WIN_RATE_CB_THRESHOLD*100:.0f}%)\n"
                f"All new entries paused for {WIN_RATE_CB_PAUSE_MINS} minutes.\n"
                f"Open positions still monitored."
            )
            save_state()

    # Exclude partial TP entries from win rate — they always show positive and skew the count
    full_trades = [t for t in trade_history if not t.get("is_partial")]
    wins        = [t for t in full_trades if t["pnl_pct"] > 0]
    win_rate    = len(wins) / len(full_trades) * 100 if full_trades else 0
    total_pnl   = sum(t["pnl_usdt"] for t in trade_history)  # total includes partials
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icons     = {
        "TAKE_PROFIT":   ("🎯","Take Profit Hit"),
        "STOP_LOSS":     ("🛑","Stop Loss Hit"),
        "TRAILING_STOP": ("📉","Trailing Stop Hit"),
        "FLAT_EXIT":     ("😴","Flat Exit"),
        "ROTATION":      ("🔀","Rotated"),
        "TIMEOUT":       ("⏰","Timeout Exit"),
        "VOL_COLLAPSE":  ("📉","Volume Collapsed"),
        "PARTIAL_TP":    ("🎯½","Partial Take Profit"),
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
        f"Session: {len(full_trades)} trades | Win: {win_rate:.0f}% | P&L: ${total_pnl:+.2f}"
    )
    log.info(f"📈 Closed {symbol} [{reason}] {pnl_pct:+.2f}% | Win:{win_rate:.0f}% P&L:${total_pnl:+.2f}")
    save_state()
    return True

# ── Heartbeat ─────────────────────────────────────────────────

def send_heartbeat(balance: float):
    global last_heartbeat_at
    if time.time() - last_heartbeat_at < 3600:
        return
    last_heartbeat_at = time.time()

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    today        = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trades_today = len([t for t in trade_history
                        if t.get("closed_at","")[:10] == today
                        and not t.get("is_partial")])

    scalper_lines = []
    for t in scalper_trades:
        try:
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
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
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
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

        r = _get_session().post(
            "https://api.anthropic.com/v1/messages",
            headers={
                "x-api-key":         ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01",
                "content-type":      "application/json",
            },
            json=body,
            timeout=30,
        )
        if not r.ok:
            log.warning(f"ask_haiku HTTP {r.status_code}: {r.text[:200]}")
            return ""
        for block in r.json().get("content", []):
            if block.get("type") == "text":
                return block["text"].strip()
    except Exception as e:
        log.warning(f"ask_haiku failed: {e}")
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

def _fetch_fills_since(symbols: list, since_ms: int) -> dict:
    """
    Fetch all myTrades for the given symbols since since_ms.
    Returns a dict of {orderId: {symbol, side, qty, cost}} aggregated across fills.
    Shared by send_daily_summary and fetch_mexc_weekly_pnl.
    """
    all_fills = []
    for sym in symbols:
        try:
            fills = private_get("/api/v3/myTrades",
                                {"symbol": sym, "startTime": since_ms, "limit": 1000})
            if fills:
                all_fills.extend(fills)
        except:
            pass
        time.sleep(0.1)
    orders = collections.defaultdict(lambda: {"symbol": "", "qty": 0, "cost": 0, "side": ""})
    for fill in all_fills:
        oid = fill["orderId"]
        orders[oid]["symbol"] = fill["symbol"]
        orders[oid]["side"]   = "BUY" if fill["isBuyer"] else "SELL"
        orders[oid]["qty"]   += float(fill["qty"])
        orders[oid]["cost"]  += float(fill["quoteQty"])
    return dict(orders)


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
        orders = _fetch_fills_since(symbols, since_ms=now_ms - 86400_000)
        if not orders:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return
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
        orders = _fetch_fills_since(symbols, since_ms=now_ms - 7 * 86400_000)
        if not orders:
            return {"error": "No fills found"}
        buys    = {o: v for o, v in orders.items() if v["side"] == "BUY"}
        sells   = {o: v for o, v in orders.items() if v["side"] == "SELL"}
        bought  = sum(v["cost"] for v in buys.values())
        sold    = sum(v["cost"] for v in sells.values())
        bsyms   = collections.Counter(v["symbol"] for v in buys.values())
        ssyms   = collections.Counter(v["symbol"] for v in sells.values())
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

def _cmd_status(balance: float):
    mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    lines = [f"📋 <b>Status</b> [{mode}]\n━━━━━━━━━━━━━━━"]
    for t in scalper_trades:
        try:
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            lines.append(f"🟢 {t['symbol']} | {pct:+.2f}% | "
                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
        except:
            lines.append(f"🟢 {t['symbol']} (unavailable)")
    if not scalper_trades:
        lines.append("Scalper: scanning...")
    for t in alt_trades:
        try:
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            lines.append(f"{t['label']}: <b>{t['symbol']}</b> | {pct:+.2f}% | "
                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
        except:
            lines.append(f"{t['label']}: {t['symbol']} (unavailable)")
    if not alt_trades:
        lines.append("Alt: scanning...")
    lines.append(f"Balance: <b>${balance:.2f} USDT</b>")
    telegram("\n".join(lines))


def _cmd_config():
    telegram(
        f"⚙️ <b>Current Config</b>\n━━━━━━━━━━━━━━━\n"
        f"🟢 <b>Scalper</b>\n"
        f"  Max: {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%\n"
        f"  TP: dynamic {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% (signal-aware, candle-capped)\n"
        f"  SL: dynamic {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}% (noise-floored)\n"
        f"  Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.1f}%\n"
        f"  Watchlist: {len(_watchlist)} pairs | age: {(time.time()-_watchlist_at)/60:.0f}min\n"
        f"\n🌙 <b>Moonshot</b>  [bot-monitored]\n"
        f"  Max: {ALT_MAX_TRADES} trades | Min budget: max($2, {MOONSHOT_BUDGET_PCT*100:.0f}% of balance)\n"
        f"  SL: -{MOONSHOT_SL*100:.0f}%  Max: {MOONSHOT_TIMEOUT_MAX_MINS}min (no limit after partial TP)\n"
        f"  Partial TP: {MOONSHOT_PARTIAL_TP_RATIO*100:.0f}% sold at +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}% → trail {MOONSHOT_TRAIL_PCT*100:.0f}% stop\n"
        f"\n🔄 <b>Reversal</b>  [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  SL: cap-candle anchor  Max: {REVERSAL_MAX_HOURS}h\n"
        f"  Partial TP: {REVERSAL_PARTIAL_TP_RATIO*100:.0f}% sold at +{REVERSAL_PARTIAL_TP_PCT*100:.1f}% → SL moves to entry\n"
        f"\n🧠 Sentiment: {'✅ on (web search)' if SENTIMENT_ENABLED and WEB_SEARCH_ENABLED else '✅ on (no web search — /ask + journal only)' if SENTIMENT_ENABLED else '⚠️ off'}\n"
        f"\n{'⏸️ PAUSED' if _paused else '▶️ RUNNING'}"
    )


def _cmd_close():
    telegram("🚨 <b>Emergency close triggered.</b>")
    closed = 0
    for t in scalper_trades[:]:
        if close_position(t, "STOP_LOSS"):
            scalper_trades.remove(t); closed += 1
    for t in alt_trades[:]:
        if close_position(t, "STOP_LOSS"):
            alt_trades.remove(t); closed += 1
    telegram(f"✅ Closed {closed} position(s).")


def _cmd_resetstreak():
    global _consecutive_losses, _win_rate_pause_until, _streak_paused_at
    _consecutive_losses    = 0
    _win_rate_pause_until  = 0.0
    _streak_paused_at      = 0.0
    run._streak_alerted    = False  # prevent stale alert flag blocking next trigger
    save_state()
    telegram("✅ <b>Streak reset.</b> Consecutive losses cleared, win-rate pause lifted. Scalper entries resumed.")


def _cmd_ask(question: str, balance: float):
    if not SENTIMENT_ENABLED:
        telegram("🧠 <b>/ask</b> requires ANTHROPIC_API_KEY to be set.")
        return
    telegram("🧠 Thinking...")
    recent = trade_history[-50:] if len(trade_history) > 50 else trade_history
    today  = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    context_lines = []
    for t in recent:
        if t.get("closed_at") and t.get("opened_at"):
            held = round((datetime.fromisoformat(t["closed_at"]) -
                          datetime.fromisoformat(t["opened_at"])).total_seconds() / 60)
            context_lines.append(
                f"{t.get('closed_at','?')[:16]} {t['symbol']} [{t['label']}] "
                f"pnl={t.get('pnl_pct',0):+.2f}% reason={t.get('exit_reason','?')} "
                f"score={t.get('score',0):.0f} rsi={t.get('rsi',0):.0f} held={held}min"
            )
    open_ctx = []
    for t in scalper_trades + alt_trades:
        try:
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
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
        + "\n".join(context_lines[-30:])
        + (f"\n\nCurrently open: {', '.join(open_ctx)}" if open_ctx else "")
        + f"\n\nBalance: ${balance:.2f} USDT | Date: {today}\n\nUser question: {question}"
    )
    answer = ask_haiku(prompt, system=system, max_tokens=300)
    if answer:
        clean_a = re.sub(r'<[^>]+>', '', answer)
        header  = f"🧠 Ask: {question}\n━━━━━━━━━━━━━━━\n"
        telegram((header + clean_a)[:4000], parse_mode="")
    else:
        telegram("🧠 Couldn't get an answer — check logs.")


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
            raw_text = msg.get("text", "").strip()
            text     = raw_text.lower()
            if str(msg.get("chat", {}).get("id")) != str(TELEGRAM_CHAT_ID):
                continue

            if   text == "/pnl":    telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))
            elif text == "/status": _cmd_status(balance)
            elif text == "/logs":
                out = ("📜 <b>Last Scanner Activity</b>\n━━━━━━━━━━━━━━━\n"
                       + "\n".join(f"<code>{l}</code>" for l in _scanner_log_buffer)
                       if _scanner_log_buffer else "📜 No scanner activity yet.")
                telegram(out)
            elif text == "/pause":  _paused = True;  telegram("⏸️ <b>Paused.</b> No new trades. Existing positions monitored.\n/resume to restart.")
            elif text == "/resume": _paused = False; telegram("▶️ <b>Resumed.</b> Scanning for new trades.")
            elif text == "/close":   _cmd_close()
            elif text == "/restart":      _cmd_restart()
            elif text == "/resetstreak":  _cmd_resetstreak()
            elif text == "/config":       _cmd_config()
            elif raw_text.startswith("/ask ") or raw_text.startswith("/ask@"):
                question = raw_text.split(" ", 1)[1].strip() if " " in raw_text else ""
                if not question:
                    telegram("🧠 Usage: <code>/ask why am I losing on flat exits?</code>")
                else:
                    _cmd_ask(question, balance)

    except Exception as e:
        log.debug(f"Telegram poll error: {e}")

# ── Startup reconciliation ─────────────────────────────────────

def reconcile_open_positions():
    """
    At startup: verify loaded state against exchange reality.

    Three checks:
    1. Balance cross-check — each loaded position must still have a non-dust
       balance on the exchange. If not, the position closed while we were down.
    2. Untracked holdings — non-dust balances with no state entry (crash mid-buy,
       manual trades). Flagged via Telegram; bot cannot monitor without entry price.
    3. Orphan orders — exchange open orders with no matching state entry.
    """
    if PAPER_TRADE:
        if scalper_trades or alt_trades:
            log.info(f"✅ [PAPER] Restored {len(scalper_trades)} scalper + {len(alt_trades)} alt trades.")
        return
    try:
        # Fetch balances once — used by all three checks below
        try:
            balances = {b["asset"]: float(b.get("free", 0)) + float(b.get("locked", 0))
                        for b in private_get("/api/v3/account").get("balances", [])}
        except Exception as e:
            log.warning(f"Balance fetch failed during reconcile: {e}")
            balances = {}

        # ── 1. Balance cross-check for loaded positions ────────────
        if scalper_trades or alt_trades:

            stale = []
            for trade in list(scalper_trades + alt_trades):
                asset = trade["symbol"].replace("USDT", "")
                held  = balances.get(asset, 0.0)
                # Dust threshold: less than 5% of expected qty means position closed on exchange
                expected_qty = trade.get("qty", 0)
                if expected_qty > 0 and held < expected_qty * 0.05:
                    stale.append(trade)
                    log.warning(f"⚠️  [{trade['label']}] {trade['symbol']}: state says "
                                f"qty={expected_qty:.4f} but exchange shows {held:.4f} — "
                                f"position likely closed while bot was down")

            if stale:
                for trade in stale:
                    # Remove from active lists and record as unknown exit
                    if trade in scalper_trades:
                        scalper_trades.remove(trade)
                    if trade in alt_trades:
                        alt_trades.remove(trade)
                    trade_history.append({
                        **{k: v for k, v in trade.items() if not k.startswith("_")},
                        "exit_price":   trade.get("entry_price", 0),
                        "exit_ticker":  trade.get("entry_price", 0),
                        "exit_reason":  "UNKNOWN_CLOSED",
                        "closed_at":    datetime.now(timezone.utc).isoformat(),
                        "fee_usdt":     0.0,
                        "cost_usdt":    trade.get("budget_used", 0),
                        "revenue_usdt": trade.get("budget_used", 0),
                        "pnl_pct":      0.0,
                        "pnl_usdt":     0.0,
                        "fills_used":   False,
                        "note":         "Closed while bot was offline — P&L unknown",
                    })
                save_state()
                syms = [t["symbol"] for t in stale]
                telegram(
                    f"⚠️ <b>Positions closed while bot was offline</b>\n"
                    f"━━━━━━━━━━━━━━━\n"
                    f"Symbols: <b>{', '.join(syms)}</b>\n"
                    f"Recorded as UNKNOWN_CLOSED — check MEXC for actual P&L.\n"
                    f"Remaining positions are being monitored normally."
                )
            elif scalper_trades or alt_trades:
                log.info(f"✅ Restored {len(scalper_trades)} scalper + {len(alt_trades)} alt trades "
                         f"— exchange balances confirmed.")

        # ── 2. Untracked holdings scan ─────────────────────────────
        # Find non-dust balances with no matching bot state.
        # Use a single batch price fetch rather than N individual calls.
        if balances:
            known_assets = {t["symbol"].replace("USDT", "") for t in scalper_trades + alt_trades}
            candidates   = [a for a, q in balances.items()
                            if a not in ("USDT", "MX") and a not in known_assets and q > 0]
            if candidates:
                try:
                    all_prices = {p["symbol"]: float(p["price"])
                                  for p in public_get("/api/v3/ticker/price")}
                except Exception:
                    all_prices = {}

                untracked = []
                for asset in candidates:
                    price = all_prices.get(f"{asset}USDT", 0.0)
                    value = balances[asset] * price
                    if value >= 5.0:
                        untracked.append(f"{asset}: {balances[asset]:.4f} (~${value:.2f})")

                if untracked:
                    log.warning(f"⚠️  Untracked holdings: {untracked}")
                    telegram(
                        f"⚠️ <b>Untracked holdings detected</b>\n━━━━━━━━━━━━━━━\n"
                        + "\n".join(untracked) + "\n\n"
                        f"These are NOT being monitored (no entry price/SL/TP in state).\n"
                        f"Could be a crash mid-buy or manual trade. Close on MEXC if unwanted."
                    )
        # ── 3. Orphan order detection ──────────────────────────────
        open_orders = private_get("/api/v3/openOrders", {})
        if not open_orders:
            return
        known_symbols = {t["symbol"] for t in scalper_trades + alt_trades}
        orphan_orders = [o for o in open_orders if o["symbol"] not in known_symbols]
        if orphan_orders:
            syms = list({o["symbol"] for o in orphan_orders})
            log.warning(f"⚠️  Found {len(orphan_orders)} orphaned order(s) with no state: {syms}")
            telegram(
                f"⚠️ <b>Orphaned orders found at startup!</b>\n━━━━━━━━━━━━━━━\n"
                f"Found {len(orphan_orders)} order(s) not in saved state: <b>{', '.join(syms)}</b>\n\n"
                f"These are NOT being monitored. Check MEXC and close manually if needed."
            )
    except Exception as e:
        log.error(f"Reconcile failed: {e}")

# ── Main loop ──────────────────────────────────────────────────

def startup() -> float:
    """
    Initialise bot on launch: load state, reconcile exchange, build watchlist,
    send the startup Telegram message. Returns startup_balance.
    """
    global scalper_trades, alt_trades, trade_history, _consecutive_losses, \
           _win_rate_pause_until, _scalper_excluded, _alt_excluded, _api_blacklist

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")

    _load_symbol_rules()

    (scalper_trades, alt_trades, trade_history,
     _consecutive_losses, _win_rate_pause_until, _streak_paused_at,
     _scalper_excluded, _alt_excluded, _api_blacklist) = load_state()

    reconcile_open_positions()

    _start_ws_monitor()  # start before watchlist build so open position prices are live

    log.info("📋 Building initial watchlist...")
    build_watchlist(fetch_tickers())

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (max {SCALPER_MAX_TRADES} × {SCALPER_BUDGET_PCT*100:.0f}%)\n"
        f"  TP/SL: dynamic (signal-aware ATR×mult, candle-capped, noise-floored)\n"
        f"  TP range: {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% | SL range: {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}%\n"
        f"  Entry threshold: score ≥ {SCALPER_THRESHOLD} | 1h vol ≥ ${SCALPER_MIN_1H_VOL:,}\n"
        f"  Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.1f}% trail\n"
        f"  Breakeven: score ≥ {SCALPER_BREAKEVEN_SCORE} → lock at +{SCALPER_BREAKEVEN_ACT*100:.1f}%\n"
        f"  Symbol cooldown: {SCALPER_SYMBOL_COOLDOWN//60}min after SL\n"
        f"  Circuit breakers: daily -{SCALPER_DAILY_LOSS_PCT*100:.0f}% | {MAX_CONSECUTIVE_LOSSES} consecutive losses\n"
        f"  Watchlist: top {WATCHLIST_SIZE} pairs, refresh every {WATCHLIST_TTL//60}min\n"
        f"\n🌙 <b>Moonshot</b> (max {ALT_MAX_TRADES} trades, {MOONSHOT_BUDGET_PCT*100:.0f}% each) [bot-monitored]\n"
        f"  SL: -{MOONSHOT_SL*100:.0f}% | Partial TP: +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}% then {MOONSHOT_TRAIL_PCT*100:.0f}% trail | max {MOONSHOT_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b> (5%) [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  max {REVERSAL_MAX_HOURS}h\n"
        f"\n🧠 <b>AI</b>: {'✅ Haiku + web search' if SENTIMENT_ENABLED and WEB_SEARCH_ENABLED else '✅ Haiku only (/ask + journal)' if SENTIMENT_ENABLED else '⚠️ disabled (set ANTHROPIC_API_KEY)'}\n"
        f"  Cache: {SENTIMENT_CACHE_MINS}min | Bonus: +{SENTIMENT_MAX_BONUS}pts | Penalty: -{SENTIMENT_MAX_PENALTY}pts\n"
        f"\n<i>/status · /pnl · /logs · /config · /pause · /resume · /close · /restart · /resetstreak · /ask</i>"
    )
    return startup_balance


def run():
    global _last_rotation_scan, _watchlist, _watchlist_at, \
           _scalper_excluded, _alt_excluded, _btc_ema_gap, \
           _streak_paused_at, _consecutive_losses, _win_rate_pause_until

    startup_balance  = startup()
    balance          = get_available_balance()

    while True:
        try:
            # ── Commands first — ensures /pause and /close respond even
            # if MEXC API calls later in the loop are slow or timing out
            listen_for_commands(balance)

            balance = get_available_balance()
            _load_symbol_rules()

            all_trades   = scalper_trades + alt_trades  # computed once, reused below
            open_symbols = {t["symbol"] for t in all_trades}

            total_value = balance
            for t in all_trades:
                if not PAPER_TRADE:
                    try:
                        px = ws_price(t["symbol"]) or float(
                            public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"]
                        )
                        total_value += px * t["qty"]
                    except:
                        total_value += t["budget_used"]
                else:
                    total_value += t["budget_used"]

            # ── Circuit breakers ──────────────────────────────────
            # Three independent gates — all block new scalper entries:
            # 1. Daily loss:    total session P&L dropped below threshold
            # 2. Loss streak:   N consecutive SLs regardless of total P&L
            # 3. Win rate:      last WIN_RATE_CB_WINDOW trades < WIN_RATE_CB_THRESHOLD win rate
            today        = datetime.now(timezone.utc).strftime("%Y-%m-%d")
            daily_pnl    = sum(t["pnl_usdt"] for t in trade_history
                               if t.get("closed_at","")[:10] == today
                               and not t.get("is_partial"))
            loss_limit   = -(startup_balance * SCALPER_DAILY_LOSS_PCT)
            daily_cb     = daily_pnl < loss_limit
            streak_cb    = _consecutive_losses >= MAX_CONSECUTIVE_LOSSES
            win_rate_cb  = time.time() < _win_rate_pause_until
            circuit_open = daily_cb or streak_cb or win_rate_cb

            if circuit_open and int(time.time()) % 300 < 3:
                if win_rate_cb:
                    mins_left = (_win_rate_pause_until - time.time()) / 60
                    log.info(f"🛑 Win-rate pause active ({mins_left:.0f}min remaining) — no new entries")
                else:
                    reason_str = (f"daily P&L ${daily_pnl:.2f}" if daily_cb
                                  else f"{_consecutive_losses} consecutive losses")
                    log.info(f"🛑 Circuit open ({reason_str}) — no new scalper entries")

            if daily_cb and not getattr(run, "_circuit_alerted_today", ""):
                run._circuit_alerted_today = today
                telegram(
                    f"🛑 <b>Daily loss limit hit</b>\n"
                    f"Session P&L: <b>${daily_pnl:.2f}</b> (limit: ${loss_limit:.2f})\n"
                    f"No new scalper entries until midnight UTC.\n"
                    f"Open positions still monitored."
                )
            elif not daily_cb:
                run._circuit_alerted_today = ""

            if streak_cb and not getattr(run, "_streak_alerted", False):
                run._streak_alerted = True
                _streak_paused_at   = time.time()
                telegram(
                    f"🛑 <b>Loss streak limit hit</b>\n"
                    f"<b>{_consecutive_losses} consecutive scalper losses.</b>\n"
                    f"Pausing new entries until a win resets the streak.\n"
                    f"Open positions still monitored."
                )
            elif not streak_cb:
                run._streak_alerted = False

            # Auto-reset streak CB after STREAK_AUTO_RESET_MINS if no open scalper positions.
            # Prevents deadlock where CB is active but no trades can win to clear it.
            if (streak_cb
                    and not scalper_trades
                    and _streak_paused_at > 0
                    and time.time() - _streak_paused_at >= STREAK_AUTO_RESET_MINS * 60):
                _consecutive_losses = 0
                _streak_paused_at   = 0.0
                run._streak_alerted = False
                save_state()
                log.info(f"✅ Streak CB auto-reset after {STREAK_AUTO_RESET_MINS}min with no open positions")
                telegram(f"✅ <b>Streak reset</b> (auto)\n"
                         f"Paused {STREAK_AUTO_RESET_MINS}min with no open positions — scalper entries resumed.")
                # Recompute so this cycle can enter without waiting 60s
                streak_cb    = False
                circuit_open = daily_cb or win_rate_cb

            # ── Max combined exposure check ───────────────────────
            # If open positions already consume MAX_EXPOSURE_PCT of balance,
            # skip new entries this cycle — don't concentrate risk further.
            open_exposure = sum(t.get("budget_used", 0) for t in all_trades)
            over_exposed  = (open_exposure / balance > MAX_EXPOSURE_PCT) if balance > 0 else False
            if over_exposed:
                log.debug(f"⚠️ Over-exposed (${open_exposure:.0f} / ${balance:.0f}) — skipping new entries")

            # ── Entry gates ───────────────────────────────────────
            # Computed before the BTC fetch so the fetch only runs when needed.
            # btc_panic is set below and fed back into these — that's fine since
            # panic only adds an extra block, never removes one.
            scalper_needs_entry = (not _paused and not circuit_open and not over_exposed
                                   and len(scalper_trades) < SCALPER_MAX_TRADES)
            alt_needs_entry     = (not _paused and not over_exposed
                                   and len(alt_trades) < ALT_MAX_TRADES)

            # ── BTC panic check — blocks ALL strategies ───────────
            # A -5% BTC candle is a market-wide event. Stop everything,
            # not just scalper. Uses the same 120-candle dataset as the
            # regime filter below — no extra fetch needed.
            btc_panic = False
            df_btc    = None  # fetched once, shared by panic + regime checks
            if scalper_needs_entry or alt_needs_entry:
                try:
                    df_btc = parse_klines("BTCUSDT", interval="5m", limit=120, min_len=105)
                    if df_btc is not None:
                        chg = (float(df_btc["close"].iloc[-1]) /
                               float(df_btc["open"].iloc[-1]) - 1)
                        if chg < -BTC_PANIC_DROP:
                            btc_panic = True
                            log.warning(f"🚨 BTC panic: {chg*100:.2f}% — ALL entries paused this cycle")
                except Exception:
                    pass

            # Apply panic gate now that btc_panic is known
            if btc_panic:
                scalper_needs_entry = False
                alt_needs_entry     = False

            need_scan = scalper_needs_entry or alt_needs_entry
            tickers             = None
            if need_scan:
                try:
                    tickers = fetch_tickers()
                except Exception as e:
                    log.warning(f"fetch_tickers failed — skipping entry scan this cycle: {e}")

            # Rebuild watchlist every WATCHLIST_TTL seconds (30 min)
            if time.time() - _watchlist_at >= WATCHLIST_TTL:
                log.info("📋 Watchlist TTL expired — rebuilding...")
                build_watchlist(tickers if tickers is not None else fetch_tickers())

            # ── Scalper ───────────────────────────────────────
            budget = round(balance * SCALPER_BUDGET_PCT, 2)

            # ── BTC regime checks + scalper entry ─────────────
            # Only runs when actually considering a scalper entry.
            # Two hard blocks (acute danger) + one soft EMA penalty (slow trend).
            btc_regime_ok  = True
            btc_ema_gap    = 0.0
            if scalper_needs_entry:
                try:
                    if df_btc is not None:
                        btc_close = df_btc["close"]

                        # 1. Hard block — last candle worse than -BTC_REGIME_DROP
                        btc_chg = (float(btc_close.iloc[-1]) /
                                   float(df_btc["open"].iloc[-1]) - 1)
                        if btc_chg < -BTC_REGIME_DROP:
                            btc_regime_ok = False
                            log.info(f"🔴 BTC regime: hard drop {btc_chg*100:.2f}% — skip entry")

                        # 2. Soft penalty — EMA gap computed here, applied to score below
                        if btc_regime_ok:
                            btc_ema     = calc_ema(btc_close, BTC_REGIME_EMA_PERIOD)
                            btc_ema_gap = (float(btc_close.iloc[-1]) / float(btc_ema.iloc[-1]) - 1)
                            _btc_ema_gap = btc_ema_gap  # expose for watchlist display

                        # 3. Hard block — vol spike ONLY when BTC is declining.
                        # High ATR on an up move = opportunity, not danger.
                        # High ATR on a down move = panic, skip entry.
                        if btc_regime_ok:
                            tr_full = pd.concat([
                                df_btc["high"] - df_btc["low"],
                                (df_btc["high"] - df_btc["close"].shift(1)).abs(),
                                (df_btc["low"]  - df_btc["close"].shift(1)).abs(),
                            ], axis=1).max(axis=1)
                            atr_series  = tr_full.ewm(alpha=1.0 / 14, adjust=False).mean()
                            btc_atr_now = float(atr_series.iloc[-1])
                            btc_atr_avg = float(atr_series.iloc[-41:-1].mean())
                            btc_declining = float(btc_close.iloc[-1]) < float(btc_close.iloc[-5])
                            if (btc_atr_avg > 0
                                    and btc_atr_now > btc_atr_avg * BTC_REGIME_VOL_MULT
                                    and btc_declining):
                                btc_regime_ok = False
                                log.info(f"🔴 BTC regime: vol spike + declining "
                                         f"ATR×{btc_atr_now/btc_atr_avg:.1f} — skip entry")
                except Exception:
                    pass  # never block entry on a BTC fetch failure

            # ── Step 1: Try to open a new scalper entry ───────
            if scalper_needs_entry and btc_regime_ok:
                opp = find_scalper_opportunity(budget,
                                               exclude=_scalper_excluded,
                                               open_symbols=open_symbols)
                # Apply EMA100 gap as a score penalty — weak entries filtered out
                # during BTC downtrends, strong entries still allowed through.
                if opp and btc_ema_gap < 0:
                    penalty = round(abs(btc_ema_gap) * BTC_REGIME_EMA_PENALTY, 1)
                    adj_score = round(opp["score"] - penalty, 2)
                    if adj_score < SCALPER_THRESHOLD:
                        log.info(f"🟡 [SCALPER] {opp['symbol']} score {opp['score']} "
                                 f"- BTC EMA penalty {penalty:.1f}pts = {adj_score} "
                                 f"— below threshold, skip")
                        opp = None
                    else:
                        log.info(f"🟡 [SCALPER] BTC EMA penalty {penalty:.1f}pts applied "
                                 f"({opp['symbol']} {opp['score']} → {adj_score})")
                        opp["score"] = adj_score

                if opp:
                    trade_budget, pre_tp, pre_sl, _, _ = calc_risk_budget(opp, balance)
                    log.info(f"💰 [SCALPER] Risk budget: ${trade_budget:.2f} "
                             f"(1% risk @ SL {pre_sl*100:.2f}%, "
                             f"cap ${round(balance*SCALPER_BUDGET_PCT,2):.2f})")
                    trade = open_position(opp, trade_budget, pre_tp, pre_sl, "SCALPER")
                    if trade:
                        scalper_trades.append(trade)
                        _scalper_excluded.pop(opp["symbol"], None)

            # ── Step 2: Check exits on ALL open scalper trades ─
            # This runs unconditionally — whether we have 1 or 3 trades,
            # whether we're entering or not, whether circuit is open or not.
            # Previously this was inside the else-branch only, meaning trades
            # with 1-2 open positions NEVER had their SL/TP/trail checked.
            if scalper_trades:
                best_opp   = None
                best_score = 0
                # Only scan for rotation candidate when at max capacity
                at_max = len(scalper_trades) >= SCALPER_MAX_TRADES
                if at_max and not circuit_open:
                    now = time.time()
                    if now - _last_rotation_scan >= ROTATION_SCAN_INTERVAL:
                        _last_rotation_scan = now
                        best_opp   = find_scalper_opportunity(budget,
                                                              exclude=_scalper_excluded,
                                                              open_symbols=open_symbols)
                        best_score = best_opp["score"] if best_opp else 0

                # Compute the worst-performing trade once — used to decide rotation target
                worst_pct = min((t.get("highest_price", t["entry_price"]) /
                                 t["entry_price"] - 1) * 100 for t in scalper_trades)
                for trade in scalper_trades[:]:
                    tpct     = (trade.get("highest_price", trade["entry_price"]) /
                                trade["entry_price"] - 1) * 100
                    s_arg    = best_score if abs(tpct - worst_pct) < 0.01 else 0

                    should_exit, reason = check_exit(trade, best_score=s_arg)
                    if should_exit:
                        if reason in ("STOP_LOSS", "TRAILING_STOP", "FLAT_EXIT", "TIMEOUT"):
                            _scalper_excluded[trade["symbol"]] = (
                                time.time() + SCALPER_SYMBOL_COOLDOWN
                            )
                            log.info(f"⏳ [SCALPER] {trade['symbol']} in cooldown "
                                     f"for {SCALPER_SYMBOL_COOLDOWN//60}min after {reason}")
                        if close_position(trade, reason):
                            scalper_trades.remove(trade)
                            if reason == "ROTATION" and best_opp:
                                rot_budget, rot_pre_tp, rot_pre_sl, _, _ = calc_risk_budget(best_opp, balance)
                                new_t = open_position(best_opp, rot_budget, rot_pre_tp, rot_pre_sl, "SCALPER")
                                if new_t:
                                    scalper_trades.append(new_t)
                                    _scalper_excluded.pop(best_opp["symbol"], None)

            # ── Alt (Moonshot / Reversal) ─────────────────────
            if not _paused and len(alt_trades) < ALT_MAX_TRADES:
                ideal  = round(total_value * MOONSHOT_BUDGET_PCT, 2)
                budget = min(ideal, balance)
                # Floor: $2 minimum — below this fees eat the position entirely.
                min_alt = MOONSHOT_MIN_NOTIONAL

                if budget < min_alt:
                    log.info(f"💰 Alt budget ${budget:.2f} below floor ${min_alt:.2f} — skipping scan")
                elif tickers is None:
                    log.debug("Alt scan skipped — tickers unavailable this cycle")
                else:
                    log.info(f"💰 Alt budget: ${budget:.2f} "
                             f"(ideal ${ideal:.2f} | free ${balance:.2f} | total ${total_value:.2f})")
                    opp = find_moonshot_opportunity(tickers, budget,
                                                    exclude=_alt_excluded,
                                                    open_symbols=open_symbols)
                    if opp:
                        # Volume-weighted position sizing — thin books get smaller positions.
                        # Scales linearly: $500k vol → 1%, $1.5M → full 3% (capped).
                        ticker_row = tickers[tickers["symbol"] == opp["symbol"]]
                        if not ticker_row.empty:
                            vol_24h = float(ticker_row["quoteVolume"].iloc[0])
                            vol_pct = min(MOONSHOT_BUDGET_PCT, vol_24h / MOONSHOT_VOL_DIVISOR)
                        else:
                            vol_24h = None
                            vol_pct = MOONSHOT_BUDGET_PCT  # ticker missing — use full budget, don't penalise
                        budget     = max(min_alt, min(round(total_value * vol_pct, 2), balance))
                        if vol_pct < MOONSHOT_BUDGET_PCT and vol_24h is not None:
                            log.info(f"💰 [MOONSHOT] Vol-weighted: "
                                     f"{vol_pct*100:.1f}% (24h vol ${vol_24h:,.0f}) → ${budget:.2f}")
                        trade = open_position(opp, budget, MOONSHOT_TP_INITIAL, MOONSHOT_SL,
                                              "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                        if trade:
                            alt_trades.append(trade); _alt_excluded = set()
                        else:
                            _alt_excluded.discard(opp["symbol"])
                    else:
                        opp = find_reversal_opportunity(tickers, budget,
                                                        exclude=_alt_excluded,
                                                        open_symbols=open_symbols)
                        if opp:
                            trade = open_position(opp, budget, REVERSAL_TP, REVERSAL_SL,
                                                  "REVERSAL", max_hours=REVERSAL_MAX_HOURS)
                            if trade:
                                alt_trades.append(trade); _alt_excluded = set()
                            else:
                                _alt_excluded.discard(opp["symbol"])

            for trade in alt_trades[:]:
                should_exit, reason = check_exit(trade)
                if should_exit:
                    if reason == "PARTIAL_TP":
                        # Sell half, update trade in place — do NOT remove from list
                        execute_partial_tp(trade)
                    else:
                        _alt_excluded.add(trade["symbol"])
                        if close_position(trade, reason):
                            alt_trades.remove(trade)

            send_heartbeat(balance)
            send_daily_summary(balance)
            send_weekly_summary(balance)
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
            save_state()
            for t in scalper_trades + alt_trades:
                log.warning(f"⚠️  Holding {t['symbol']} ({t['label']}) — close manually if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nRetrying in 30s.")
            time.sleep(30)

run()
