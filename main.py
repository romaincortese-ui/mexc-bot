"""
MEXC Trading Bot — 5 Strategies + Adaptive Learning + High-ROI Engine Upgrades
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Added features (restored in this version):
  • Fixed Trinity budget calculation (uses allocated capital, not total value)
  • Oversold (30005) error handling – treats as already closed without spam
  • Improved close_position retry logic with progressive delays and limit fallback
  • DUST_THRESHOLD – stops endless loops on positions < $5 (default)
  • Dust prevention in partial TP – if remaining slice < dust, sell 100%
  • MAJOR_FILL_THRESHOLD – detect 85%+ fills and close trade immediately
  • Major partial fill notification – sends TP hit alert on high fill rates
  • Emergency market liquidation with up to 5 retries
  • Alert de‑duplication – prevents spam for the same symbol within 10 minutes
  • “Mission Over” threshold – switches to market sell if trade is already partially filled
  • Dust closure now sends a Telegram alert (so you never miss a final exit)
  • Context‑aware exits:
      - Defensive stops (SL, trailing, timeout, etc.) cancel all orders first, then market sell
      - Moonshot TPs use a 1‑second hammer (limit → market after 1s)
      - Scalper TPs keep patient maker orders
  • Capital allocation per strategy (Scalper 25%, Moonshot/Reversal 50%, Trinity 25%)
  • Maker orders (post-only limit) for both entry and TP to reduce fees
  • ATR-based moonshot stop-loss
  • Reduced partial TP ratio for moonshots
  • Dynamic disable of micro/partial TP for trades below MIN_TRADE_FOR_PARTIAL_TP
  • Kelly uncap up to 2.8% risk on high-confidence setups
  • Stricter rotation (+13 gap, 15min cooldown)
  • BTC volatility guard (ATR ratio >1.85 → pause scalper entries)
  • Micro‑cap quick trigger (low volume moonshots protect early)
  • Dynamic ATR‑based giveback for moonshot HWM stops
  • Locked balance handling (free+locked) to prevent premature exit
  • Market regime detection (adjusts entry thresholds based on BTC volatility/trend)
  • Chase limit orders for profit exits (reduces slippage)
  • Balance verification on close – retries until position is actually gone
  • FLOOR & CHASE EXIT STRATEGY (MOONSHOT / REVERSAL / PRE‑BREAKOUT):
      - After a micro or partial TP, a hard profit floor (true breakeven or 0.5% below exit)
        and a dynamic trailing stop (based on ATR and high‑water mark) are activated.
      - Exit is triggered when price hits the higher of the two, and execution uses
        chase limit orders (avoiding market sell unless absolutely necessary).
  • CRITICAL FIXES IN CLOSE_POSITION:
      - Added 1.5s delay after cancel_all_orders to let MEXC unlock funds.
      - Non‑defensive exits now verify success; if partial fill, fallback to market sell.
      - Trade removed only when fully closed; otherwise kept in memory for retry.
"""

import time, hmac, hashlib, logging, logging.handlers, requests, json, os, threading, collections, re, math
import asyncio
import urllib.parse
from decimal import Decimal, ROUND_DOWN
import pandas as pd
import numpy as np
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG (updated with capital allocation)
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = os.getenv("MEXC_API_KEY",    "your_api_key_here")
MEXC_API_SECRET = os.getenv("MEXC_API_SECRET", "your_api_secret_here")

PAPER_TRADE   = os.getenv("PAPER_TRADE", "False").lower() == "true"
PAPER_BALANCE = float(os.getenv("PAPER_BALANCE", "50"))

# Capital allocation (percentages of total balance)
SCALPER_ALLOCATION_PCT   = float(os.getenv("SCALPER_ALLOCATION_PCT",   "0.25"))
MOONSHOT_ALLOCATION_PCT  = float(os.getenv("MOONSHOT_ALLOCATION_PCT",  "0.50"))
TRINITY_ALLOCATION_PCT   = float(os.getenv("TRINITY_ALLOCATION_PCT",   "0.25"))

# Minimum trade size for enabling micro/partial TP (to avoid dust)
MIN_TRADE_FOR_PARTIAL_TP = float(os.getenv("MIN_TRADE_FOR_PARTIAL_TP", "15.0"))

# ── Maker orders (post‑only) for both entry and TP ─────────────
USE_MAKER_ORDERS = os.getenv("USE_MAKER_ORDERS", "True").lower() == "true"
MAKER_ORDER_TIMEOUT_SEC = float(os.getenv("MAKER_ORDER_TIMEOUT_SEC", "2.5"))

# Chase limit order settings (for exits)
CHASE_LIMIT_TIMEOUT = float(os.getenv("CHASE_LIMIT_TIMEOUT", "2.5"))
CHASE_LIMIT_RETRIES = int(os.getenv("CHASE_LIMIT_RETRIES", "3"))

# ── Dust threshold – positions below this USD value are considered closed ──
DUST_THRESHOLD = float(os.getenv("DUST_THRESHOLD", "3.0"))

# ── Major fill threshold – if a limit order is ≥ this % filled, close trade ──
MAJOR_FILL_THRESHOLD = float(os.getenv("MAJOR_FILL_THRESHOLD", "0.85"))

# ── Micro‑cap quick trigger (low volume moonshots) ────────────
MICRO_CAP_VOL_RATIO_THRESHOLD = float(os.getenv("MICRO_CAP_VOL_RATIO_THRESHOLD", "0.30"))
MICRO_CAP_PROTECT_ACT = float(os.getenv("MICRO_CAP_PROTECT_ACT", "0.025"))          # 2.5%
MICRO_CAP_GIVEBACK    = float(os.getenv("MICRO_CAP_GIVEBACK", "0.005"))             # 0.5%

# ── Dynamic ATR giveback multiplier (for normal moonshots) ────
MOONSHOT_HWM_ATR_MULT = float(os.getenv("MOONSHOT_HWM_ATR_MULT", "1.5"))

# ── Market regime thresholds (adjust entry thresholds) ────────
REGIME_HIGH_VOL_ATR_RATIO = float(os.getenv("REGIME_HIGH_VOL_ATR_RATIO", "1.85"))
REGIME_LOW_VOL_ATR_RATIO  = float(os.getenv("REGIME_LOW_VOL_ATR_RATIO",  "0.80"))
REGIME_STRONG_UPTREND_GAP = float(os.getenv("REGIME_STRONG_UPTREND_GAP", "0.01"))   # 1% above EMA
REGIME_STRONG_DOWNTREND_GAP = float(os.getenv("REGIME_STRONG_DOWNTREND_GAP", "-0.01")) # 1% below EMA
REGIME_TIGHTEN_MULT = float(os.getenv("REGIME_TIGHTEN_MULT", "1.25"))  # raises threshold in bad conditions
REGIME_LOOSEN_MULT  = float(os.getenv("REGIME_LOOSEN_MULT",  "0.85"))  # lowers threshold in good conditions
REGIME_TREND_MULT   = float(os.getenv("REGIME_TREND_MULT",   "0.90"))  # lowers threshold in uptrend (momentum works)

# ── Scalper (max 3 concurrent) ────────────────────────────────
SCALPER_MAX_TRADES   = int(os.getenv("SCALPER_MAX_TRADES",   "3"))
SCALPER_BUDGET_PCT   = float(os.getenv("SCALPER_BUDGET_PCT", "0.37"))   # per‑trade max % of allocated capital
SCALPER_RISK_PER_TRADE = float(os.getenv("SCALPER_RISK_PER_TRADE", "0.01"))
SCALPER_TRAIL_ACT    = float(os.getenv("SCALPER_TRAIL_ACT",    "0.03"))
SCALPER_TRAIL_PCT    = float(os.getenv("SCALPER_TRAIL_PCT",     "0.015"))
SCALPER_TRAIL_ATR_MULT = float(os.getenv("SCALPER_TRAIL_ATR_MULT", "1.85"))
SCALPER_TRAIL_MIN    = float(os.getenv("SCALPER_TRAIL_MIN",   "0.010"))
SCALPER_TRAIL_MAX    = float(os.getenv("SCALPER_TRAIL_MAX",   "0.035"))
SCALPER_CONFLUENCE_BONUS = float(os.getenv("SCALPER_CONFLUENCE_BONUS", "15"))
SCALPER_ATR_PERIOD   = 21
SCALPER_FLAT_MINS    = int(os.getenv("SCALPER_FLAT_MINS",     "25"))
SCALPER_FLAT_RANGE   = float(os.getenv("SCALPER_FLAT_RANGE",  "0.008"))
SCALPER_ROTATE_GAP   = int(os.getenv("SCALPER_ROTATE_GAP",    "25"))
SCALPER_MIN_VOL      = 500_000
SCALPER_MIN_PRICE    = 0.01
SCALPER_MIN_CHANGE   = 0.1
SCALPER_THRESHOLD    = int(os.getenv("SCALPER_THRESHOLD", "37"))
SCALPER_MAX_RSI      = int(os.getenv("SCALPER_MAX_RSI",      "70"))
WATCHLIST_MIN_SCORE  = max(5, SCALPER_THRESHOLD // 2)
SCALPER_BREAKEVEN_SCORE = int(os.getenv("SCALPER_BREAKEVEN_SCORE", "50"))
SCALPER_BREAKEVEN_ACT   = float(os.getenv("SCALPER_BREAKEVEN_ACT", "0.015"))
SCALPER_MIN_1H_VOL      = int(os.getenv("SCALPER_MIN_1H_VOL",   "50000"))
SCALPER_SYMBOL_COOLDOWN = int(os.getenv("SCALPER_SYMBOL_COOLDOWN", "1200"))
SCALPER_DAILY_LOSS_PCT  = 0.05
SCALPER_EMA50_PENALTY  = float(os.getenv("SCALPER_EMA50_PENALTY", "200"))
SCALPER_MAX_CORRELATION = float(os.getenv("SCALPER_MAX_CORRELATION", "0.70"))

# ── Dynamic TP/SL multipliers ─────────────────────────────────
SCALPER_TP_MULT_CROSSOVER = 2.5
SCALPER_TP_MULT_VOL_SPIKE = float(os.getenv("SCALPER_TP_MULT_VOL_SPIKE", "1.8"))
SCALPER_TP_MULT_OVERSOLD  = 2.2
SCALPER_TP_MULT_DEFAULT   = 2.0
SCALPER_TP_CANDLE_MULT    = 4.0
SCALPER_TP_MIN            = float(os.getenv("SCALPER_TP_MIN",  "0.030"))
SCALPER_TP_MAX            = float(os.getenv("SCALPER_TP_MAX",  "0.08"))
SCALPER_SL_MULT_VOL_SPIKE = 1.0
SCALPER_SL_MULT_OVERSOLD  = 1.0
SCALPER_SL_MULT_HIGH_CONF = 1.8
SCALPER_SL_MULT_DEFAULT   = float(os.getenv("SCALPER_SL_MULT_DEFAULT", "1.3"))
SCALPER_SL_NOISE_MULT     = 2.0
SCALPER_SL_MAX            = 0.04
SCALPER_SL_MIN            = 0.015

# ── Watchlist / BTC pulse ─────────────────────────────────────
WATCHLIST_SIZE      = 30
WATCHLIST_TTL       = 600
WATCHLIST_SURGE_SIZE = int(os.getenv("WATCHLIST_SURGE_SIZE", "40"))
BTC_REBOUND_PCT          = float(os.getenv("BTC_REBOUND_PCT",          "0.01"))
BTC_REBOUND_CONFIRM_PCTS = float(os.getenv("BTC_REBOUND_CONFIRM_PCTS", "0.005"))
WATCHLIST_REBOUND_MIN_INTERVAL = int(os.getenv("WATCHLIST_REBOUND_MIN_INTERVAL", "300"))

# ── Moonshot (optimized for profit capture) ──────────────────
ALT_MAX_TRADES      = 2   # maximum moonshot + reversal combined
MOONSHOT_BUDGET_PCT   = float(os.getenv("MOONSHOT_BUDGET_PCT",   "0.048"))   # per‑trade max % of allocated capital
MOONSHOT_TP_INITIAL           = float(os.getenv("MOONSHOT_TP_INITIAL", "0.10"))
MOONSHOT_SL           = float(os.getenv("MOONSHOT_SL",           "0.08"))           # fallback
MOONSHOT_SL_ATR_MULT  = float(os.getenv("MOONSHOT_SL_ATR_MULT",  "2.3"))           # ATR multiplier for SL
MOONSHOT_MAX_VOL_RATIO = float(os.getenv("MOONSHOT_MAX_VOL_RATIO", "100000"))
MOONSHOT_MIN_VOL      = int(os.getenv("MOONSHOT_MIN_VOL", "50000"))
MOONSHOT_MIN_SCORE    = 30
MOONSHOT_MAX_RSI      = float(os.getenv("MOONSHOT_MAX_RSI",      "73"))
MOONSHOT_MIN_RSI      = float(os.getenv("MOONSHOT_MIN_RSI",      "35"))
MOONSHOT_RSI_ACCEL_MIN= float(os.getenv("MOONSHOT_RSI_ACCEL_MIN","60"))
MOONSHOT_RSI_ACCEL_DELTA=float(os.getenv("MOONSHOT_RSI_ACCEL_DELTA","2"))
MOONSHOT_REBOUND_MAX_RSI   = float(os.getenv("MOONSHOT_REBOUND_MAX_RSI",   "78"))
MOONSHOT_REBOUND_VOL_RATIO = float(os.getenv("MOONSHOT_REBOUND_VOL_RATIO",  "2.0"))
MOONSHOT_REBOUND_RSI_DELTA = float(os.getenv("MOONSHOT_REBOUND_RSI_DELTA",  "3.0"))
MOONSHOT_MIN_NOTIONAL = float(os.getenv("MOONSHOT_MIN_NOTIONAL", "2.0"))
MOONSHOT_MAX_HOURS  = 2
MOONSHOT_MIN_DAYS   = 2
MOONSHOT_NEW_DAYS   = 14
MOONSHOT_MIN_VOL_RATIO = float(os.getenv("MOONSHOT_MIN_VOL_RATIO", "1.2"))
VOL_ZSCORE_MIN       = float(os.getenv("VOL_ZSCORE_MIN",       "2.0"))
VOL_RATIO_FLOOR      = float(os.getenv("VOL_RATIO_FLOOR",      "1.5"))
MOONSHOT_LIQUIDITY_RATIO = float(os.getenv("MOONSHOT_LIQUIDITY_RATIO", "200"))
MOONSHOT_TIMEOUT_FLAT_MINS   = int(os.getenv("MOONSHOT_TIMEOUT_FLAT_MINS",    "35"))
MOONSHOT_TIMEOUT_MARGINAL_MINS= int(os.getenv("MOONSHOT_TIMEOUT_MARGINAL_MINS","50"))
MOONSHOT_TIMEOUT_MAX_MINS    = int(os.getenv("MOONSHOT_TIMEOUT_MAX_MINS",     "120"))
MOONSHOT_PARTIAL_TP_PCT      = float(os.getenv("MOONSHOT_PARTIAL_TP_PCT",   "0.06"))
MOONSHOT_PARTIAL_TP_RATIO    = float(os.getenv("MOONSHOT_PARTIAL_TP_RATIO", "0.40"))
MOONSHOT_BREAKEVEN_ACT       = float(os.getenv("MOONSHOT_BREAKEVEN_ACT", "0.02"))
MOONSHOT_MICRO_TP_PCT        = float(os.getenv("MOONSHOT_MICRO_TP_PCT",   "0.025"))
MOONSHOT_MICRO_TP_RATIO      = float(os.getenv("MOONSHOT_MICRO_TP_RATIO", "0.30"))
MICRO_TP_MIN_PROFIT          = float(os.getenv("MICRO_TP_MIN_PROFIT",     "1.0"))    # min $ profit to trigger micro TP
MOONSHOT_PROTECT_ACT     = float(os.getenv("MOONSHOT_PROTECT_ACT",     "0.04"))
MOONSHOT_PROTECT_GIVEBACK = float(os.getenv("MOONSHOT_PROTECT_GIVEBACK","0.015"))  # floor for dynamic ATR giveback
MOONSHOT_BTC_EMA_GATE    = float(os.getenv("MOONSHOT_BTC_EMA_GATE",    "-0.02"))  # skip moonshot if BTC EMA gap below this

# ── Pre-Breakout (unchanged) ──────────────────────────────────
PRE_BREAKOUT_TP             = float(os.getenv("PRE_BREAKOUT_TP",             "0.08"))
PRE_BREAKOUT_SL             = float(os.getenv("PRE_BREAKOUT_SL",             "0.03"))
PRE_BREAKOUT_MAX_HOURS      = int(os.getenv("PRE_BREAKOUT_MAX_HOURS",        "3"))
PRE_BREAKOUT_MIN_VOL        = int(os.getenv("PRE_BREAKOUT_MIN_VOL",          "100000"))
PRE_BREAKOUT_ACCUM_CANDLES  = int(os.getenv("PRE_BREAKOUT_ACCUM_CANDLES",    "5"))
PRE_BREAKOUT_ACCUM_PRICE_RANGE = float(os.getenv("PRE_BREAKOUT_ACCUM_PRICE_RANGE", "0.01"))
PRE_BREAKOUT_SQUEEZE_LOOKBACK  = int(os.getenv("PRE_BREAKOUT_SQUEEZE_LOOKBACK",  "20"))
PRE_BREAKOUT_BASE_TESTS     = int(os.getenv("PRE_BREAKOUT_BASE_TESTS",       "2"))

# ── Dead coin / depth (unchanged) ─────────────────────────────
DEAD_COIN_VOL_SCALPER     = int(os.getenv("DEAD_COIN_VOL_SCALPER",    "500000"))
DEAD_COIN_VOL_MOONSHOT    = int(os.getenv("DEAD_COIN_VOL_MOONSHOT",   "150000"))
DEAD_COIN_SPREAD_MAX      = float(os.getenv("DEAD_COIN_SPREAD_MAX",   "0.003"))
DEAD_COIN_CONSECUTIVE     = int(os.getenv("DEAD_COIN_CONSECUTIVE",    "3"))
DEAD_COIN_BLACKLIST_HOURS = int(os.getenv("DEAD_COIN_BLACKLIST_HOURS","24"))
SCALPER_TRAIL_ATR_ACTIVATE = float(os.getenv("SCALPER_TRAIL_ATR_ACTIVATE", "2.0"))

# ── Progressive trail (tightens as profit grows, adjusts for volatility) ──
# Moonshot/Reversal/PreBreakout (Floor & Chase)
PROG_TRAIL_CEILING     = float(os.getenv("PROG_TRAIL_CEILING",      "0.050"))   # trail % at low profit
PROG_TRAIL_FLOOR       = float(os.getenv("PROG_TRAIL_FLOOR",        "0.018"))   # minimum trail % for big runners
PROG_TRAIL_TIGHTEN     = float(os.getenv("PROG_TRAIL_TIGHTEN",      "0.25"))    # tighten rate per unit of profit
PROG_TRAIL_VOL_ANCHOR  = float(os.getenv("PROG_TRAIL_VOL_ANCHOR",   "0.020"))   # ATR reference for vol adjustment
PROG_TRAIL_VOL_MIN     = float(os.getenv("PROG_TRAIL_VOL_MIN",      "0.70"))    # min vol multiplier (low-vol coins)
PROG_TRAIL_VOL_MAX     = float(os.getenv("PROG_TRAIL_VOL_MAX",      "1.40"))    # max vol multiplier (high-vol coins)
# Scalper progressive trail
SCALPER_PROG_CEILING   = float(os.getenv("SCALPER_PROG_CEILING",    "0.035"))   # trail % at low profit
SCALPER_PROG_FLOOR     = float(os.getenv("SCALPER_PROG_FLOOR",      "0.012"))   # minimum trail % for runners
SCALPER_PROG_TIGHTEN   = float(os.getenv("SCALPER_PROG_TIGHTEN",    "0.40"))    # tighten rate (faster for scalpers)
SCALPER_PARTIAL_TP_SCORE     = int(os.getenv("SCALPER_PARTIAL_TP_SCORE",     "79"))
SCALPER_PARTIAL_TP_RATIO     = float(os.getenv("SCALPER_PARTIAL_TP_RATIO",   "0.30"))
KELTNER_ATR_MULT   = float(os.getenv("KELTNER_ATR_MULT",   "3.0"))
KELTNER_SCORE_BONUS= float(os.getenv("KELTNER_SCORE_BONUS","10"))
REVERSAL_TP              = float(os.getenv("REVERSAL_TP",              "0.035"))
REVERSAL_SL              = float(os.getenv("REVERSAL_SL",              "0.020"))
REVERSAL_MIN_VOL         = 100_000
REVERSAL_MAX_RSI         = int(os.getenv("REVERSAL_MAX_RSI",         "38"))
REVERSAL_MIN_DROP        = float(os.getenv("REVERSAL_MIN_DROP",      "3.0"))
REVERSAL_MAX_HOURS       = 2
REVERSAL_BOUNCE_RECOVERY = 0.30
REVERSAL_VOL_RECOVERY    = 1.20
REVERSAL_CAP_SL_BUFFER   = 0.005
REVERSAL_SL_MAX          = 0.050
REVERSAL_PARTIAL_TP_PCT  = float(os.getenv("REVERSAL_PARTIAL_TP_PCT",  "0.020"))
REVERSAL_PARTIAL_TP_RATIO= float(os.getenv("REVERSAL_PARTIAL_TP_RATIO","0.60"))
REVERSAL_WEAK_BOUNCE_MINS = int(os.getenv("REVERSAL_WEAK_BOUNCE_MINS", "20"))
REVERSAL_WEAK_BOUNCE_PCT  = float(os.getenv("REVERSAL_WEAK_BOUNCE_PCT", "0.65"))

TRINITY_SYMBOLS       = ["SOLUSDT", "ETHUSDT", "BTCUSDT"]
TRINITY_BUDGET_PCT    = float(os.getenv("TRINITY_BUDGET_PCT",   "0.20"))   # per‑trade % of allocated Trinity capital
TRINITY_MAX_CONCURRENT = int(os.getenv("TRINITY_MAX_CONCURRENT", "2"))
TRINITY_DROP_PCT      = float(os.getenv("TRINITY_DROP_PCT",     "0.03"))
TRINITY_MIN_RSI       = float(os.getenv("TRINITY_MIN_RSI",      "20"))
TRINITY_MAX_RSI       = float(os.getenv("TRINITY_MAX_RSI",      "45"))
TRINITY_TP_ATR_MULT   = float(os.getenv("TRINITY_TP_ATR_MULT",  "2.0"))
TRINITY_SL_ATR_MULT   = float(os.getenv("TRINITY_SL_ATR_MULT",  "1.2"))
TRINITY_SL_MAX        = float(os.getenv("TRINITY_SL_MAX",       "0.04"))
TRINITY_TP_MIN        = float(os.getenv("TRINITY_TP_MIN",       "0.015"))
TRINITY_MAX_HOURS     = int(os.getenv("TRINITY_MAX_HOURS",      "48"))
TRINITY_VOL_BURST     = float(os.getenv("TRINITY_VOL_BURST",    "1.0"))
TRINITY_BREAKEVEN_ACT = float(os.getenv("TRINITY_BREAKEVEN_ACT","0.012"))
TRINITY_INTERVAL      = os.getenv("TRINITY_INTERVAL",           "1h")
TRINITY_DROP_LOOKBACK_CANDLES = [16, 32, 48, 96]  # 16h, 32h, 2d, 4d on 1h candles
MIN_PRICE         = 0.001
SCAN_INTERVAL     = 60
STATE_FILE        = "state.json"

# ── Adaptive learning (unchanged) ────────────────────────────
MATURITY_LOOKBACK       = int(os.getenv("MATURITY_LOOKBACK",       "20"))
MATURITY_PENALTY_MULT   = float(os.getenv("MATURITY_PENALTY_MULT", "0.5"))
MATURITY_THRESHOLD      = float(os.getenv("MATURITY_THRESHOLD",    "0.75"))
MATURITY_MOONSHOT_THRESHOLD = float(os.getenv("MATURITY_MOONSHOT_THRESHOLD", "0.85"))
MOMENTUM_DECAY_CANDLES  = int(os.getenv("MOMENTUM_DECAY_CANDLES",   "6"))
MOMENTUM_DECAY_PRICE_RANGE = float(os.getenv("MOMENTUM_DECAY_PRICE_RANGE", "0.003"))
MOMENTUM_DECAY_MIN_HELD = float(os.getenv("MOMENTUM_DECAY_MIN_HELD", "10"))
ADAPTIVE_WINDOW         = int(os.getenv("ADAPTIVE_WINDOW",         "16"))
ADAPTIVE_TIGHTEN_STEP   = float(os.getenv("ADAPTIVE_TIGHTEN_STEP", "3"))
ADAPTIVE_RELAX_STEP     = float(os.getenv("ADAPTIVE_RELAX_STEP",   "2"))
ADAPTIVE_MAX_OFFSET     = float(os.getenv("ADAPTIVE_MAX_OFFSET",   "10"))
ADAPTIVE_MIN_OFFSET     = float(os.getenv("ADAPTIVE_MIN_OFFSET",   "-5"))
PERF_REBALANCE_TRADES   = int(os.getenv("PERF_REBALANCE_TRADES",   "20"))
PERF_SCALPER_FLOOR      = float(os.getenv("PERF_SCALPER_FLOOR",    "0.10"))
PERF_SCALPER_CEIL       = float(os.getenv("PERF_SCALPER_CEIL",     "0.40"))
PERF_MOONSHOT_FLOOR     = float(os.getenv("PERF_MOONSHOT_FLOOR",   "0.02"))
PERF_MOONSHOT_CEIL      = float(os.getenv("PERF_MOONSHOT_CEIL",    "0.14"))
PERF_SHIFT_STEP         = float(os.getenv("PERF_SHIFT_STEP",       "0.028"))
FEE_RATE_TAKER          = float(os.getenv("FEE_RATE_TAKER",        "0.001"))
FEE_SLIPPAGE_BUFFER     = float(os.getenv("FEE_SLIPPAGE_BUFFER",   "0.002"))
GIVEBACK_TARGET_LOW     = float(os.getenv("GIVEBACK_TARGET_LOW",    "0.25"))
GIVEBACK_TARGET_HIGH    = float(os.getenv("GIVEBACK_TARGET_HIGH",   "0.30"))
TELEGRAM_TOKEN   = os.getenv("TELEGRAM_TOKEN",   "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")
HTTP_RETRIES           = 3
HTTP_RETRY_DELAY       = 1.0
HTTP_TRANSIENT_CODES   = {429, 500, 502, 503, 504}
KLINE_CACHE_TTL        = 30
MAX_KLINE_CACHE        = 500
API_FAIL_THRESHOLD     = 5
API_FAIL_SLEEP_BASE    = 30
API_FAIL_SLEEP_MAX     = 300
FILL_QTY_TOLERANCE     = 1.02
SCALPER_MAX_SPREAD     = 0.004
SCALPER_MIN_ATR_PCT    = float(os.getenv("SCALPER_MIN_ATR_PCT",  "0.003"))
DEPTH_BID_LEVELS    = int(os.getenv("DEPTH_BID_LEVELS",    "20"))
DEPTH_PCT_RANGE     = float(os.getenv("DEPTH_PCT_RANGE",   "0.02"))
DEPTH_BID_RATIO     = float(os.getenv("DEPTH_BID_RATIO",   "3.0"))
REVERSAL_FLAT_MINS     = int(os.getenv("REVERSAL_FLAT_MINS",     "45"))
REVERSAL_FLAT_PROGRESS = float(os.getenv("REVERSAL_FLAT_PROGRESS","0.40"))
KELLY_MULT_MARGINAL  = float(os.getenv("KELLY_MULT_MARGINAL",  "0.50"))
KELLY_MULT_SOLID     = float(os.getenv("KELLY_MULT_SOLID",     "0.80"))
KELLY_MULT_STANDARD  = float(os.getenv("KELLY_MULT_STANDARD",  "1.00"))
KELLY_MULT_HIGH_CONF = float(os.getenv("KELLY_MULT_HIGH_CONF", "1.50"))
MAX_CONSECUTIVE_LOSSES = int(os.getenv("MAX_CONSECUTIVE_LOSSES", "4"))
STREAK_AUTO_RESET_MINS = int(os.getenv("STREAK_AUTO_RESET_MINS", "60"))
WIN_RATE_CB_WINDOW     = int(os.getenv("WIN_RATE_CB_WINDOW",     "10"))
WIN_RATE_CB_THRESHOLD  = float(os.getenv("WIN_RATE_CB_THRESHOLD","0.30"))
WIN_RATE_CB_PAUSE_MINS = int(os.getenv("WIN_RATE_CB_PAUSE_MINS", "60"))
MAX_EXPOSURE_PCT       = float(os.getenv("MAX_EXPOSURE_PCT",     "0.80"))

# ── Session P&L pause (P2) ────────────────────────────────────
SESSION_LOSS_PAUSE_PCT  = float(os.getenv("SESSION_LOSS_PAUSE_PCT",  "0.03"))   # pause all if session P&L < -3%
SESSION_LOSS_PAUSE_MINS = int(os.getenv("SESSION_LOSS_PAUSE_MINS",   "120"))    # pause for 2h

# ── Per-strategy loss streak (P6) ─────────────────────────────
STRATEGY_LOSS_STREAK_MAX  = int(os.getenv("STRATEGY_LOSS_STREAK_MAX",  "3"))    # 3 losses → pause strategy
STRATEGY_LOSS_STREAK_MINS = int(os.getenv("STRATEGY_LOSS_STREAK_MINS", "240"))  # pause for 4h

# ── BTC gate hysteresis (P3) ──────────────────────────────────
MOONSHOT_BTC_GATE_REOPEN  = float(os.getenv("MOONSHOT_BTC_GATE_REOPEN", "-0.01"))  # reopen at -1%
MOONSHOT_MAX_SPREAD    = float(os.getenv("MOONSHOT_MAX_SPREAD",    "0.008"))
BTC_REGIME_EMA_PERIOD  = 100
BTC_REGIME_EMA_PENALTY = float(os.getenv("BTC_REGIME_EMA_PENALTY", "420"))
BTC_PANIC_DROP         = 0.05
ANTHROPIC_API_KEY    = os.getenv("ANTHROPIC_API_KEY", "")
SENTIMENT_ENABLED    = bool(ANTHROPIC_API_KEY)
WEB_SEARCH_ENABLED   = os.getenv("WEB_SEARCH_ENABLED", "false").lower() == "true"
SENTIMENT_CACHE_MINS = 30
SENTIMENT_MAX_BONUS  = 15
SENTIMENT_MAX_PENALTY= 20
MOONSHOT_SOCIAL_SCAN_MINS  = int(os.getenv("MOONSHOT_SOCIAL_SCAN_MINS",  "99999"))
MOONSHOT_SOCIAL_MAX_COINS  = int(os.getenv("MOONSHOT_SOCIAL_MAX_COINS",  "10"))
MOONSHOT_SOCIAL_BOOST_MAX  = int(os.getenv("MOONSHOT_SOCIAL_BOOST_MAX",  "20"))
MOONSHOT_SOCIAL_CACHE_MINS = int(os.getenv("MOONSHOT_SOCIAL_CACHE_MINS", "20"))

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

# ── State (unchanged) ──────────────────────────────────────
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
_liquidity_blacklist: dict = {}
_liquidity_fail_count: dict = {}
_scanner_log_buffer   = collections.deque(maxlen=5)
_paused               = False
_last_rotation_scan    = 0.0
ROTATION_SCAN_INTERVAL = 30
_adaptive_offsets: dict = {"SCALPER": 0.0, "MOONSHOT": 0.0}
_last_rebalance_count  = 0
_dynamic_scalper_budget: float | None  = None
_dynamic_moonshot_budget: float | None = None
_new_listings_cache    = []
_new_listings_cache_at = 0.0
NEW_LISTINGS_CACHE_TTL = 300
_watchlist             = []
_watchlist_at          = 0.0
_last_rebound_rebuild  = 0.0
_sentiment_cache: dict = {}
_sentiment_lock        = threading.Lock()
_kline_cache: dict = {}
_kline_cache_lock  = threading.Lock()
_thread_local = threading.local()
_api_fail_count   = 0
_api_fail_alerted = False
_consecutive_losses   = 0
_win_rate_pause_until = 0.0
_streak_paused_at     = 0.0
_moonshot_scan_sem = threading.Semaphore(5)
_scalper_excluded: dict = {}
_alt_excluded:     set  = set()
_trending_coins:      list  = []
_trending_coins_at:   float = 0.0
_social_boost_cache:  dict  = {}
_btc_ema_gap:         float = 0.0
_btc_ema_gap_macro:   float = 0.0  # 1h EMA gap for moonshot macro gate
_moonshot_gate_open:  bool  = True  # hysteresis state for BTC gate
_session_loss_paused_until: float = 0.0  # timestamp when session loss pause expires
_strategy_loss_streaks: dict = {}   # {"TRINITY": 2, "REVERSAL": 0, ...}
_strategy_paused_until: dict = {}   # {"TRINITY": timestamp, ...}
_fast_cycle_counter = 0
MAX_FAST_CYCLES = 10
_market_regime_mult = 1.0   # default neutral

# ── Alert de‑duplication ─────────────────────────────────────
_last_error_time: dict = {}      # symbol -> last time an error alert was sent
ERROR_ALERT_COOLDOWN = 600       # 10 minutes

# ── WebSocket monitor (unchanged) ───────────────────────────
WS_URL          = "wss://wbs-api.mexc.com/ws"
WS_PING_SECS    = 20
WS_STALE_SECS   = 60
_live_prices: dict = {}
_ws_lock           = threading.Lock()

# ── Floor & Chase (true breakeven) ────────────────────────────
def calculate_true_breakeven(entry_price: float) -> float:
    round_trip_cost = (FEE_RATE_TAKER * 2) + FEE_SLIPPAGE_BUFFER
    return entry_price * (1 + round_trip_cost)

def calc_progressive_trail(peak_profit: float, atr_pct: float,
                           ceiling: float = None, floor: float = None,
                           tighten: float = None, strategy: str = "MOONSHOT") -> float:
    """
    Compute a trail % that tightens smoothly as profit grows, and widens for volatile coins.

    At low profit  → wide trail (let it breathe)
    At high profit → tight trail (lock gains)
    High ATR       → widen slightly (avoid shakeouts)
    Low ATR        → tighten slightly (grind = tighter exit)

    Returns trail as a fraction (e.g. 0.03 = 3%).
    """
    if strategy == "SCALPER":
        c = ceiling or SCALPER_PROG_CEILING
        f = floor   or SCALPER_PROG_FLOOR
        t = tighten or SCALPER_PROG_TIGHTEN
    else:
        c = ceiling or PROG_TRAIL_CEILING
        f = floor   or PROG_TRAIL_FLOOR
        t = tighten or PROG_TRAIL_TIGHTEN

    # Base trail: linear tightening from ceiling toward floor as profit grows
    base = max(f, c - peak_profit * t)

    # Volatility adjustment: high-ATR coins get wider trails
    vol_ratio = atr_pct / PROG_TRAIL_VOL_ANCHOR if PROG_TRAIL_VOL_ANCHOR > 0 else 1.0
    vol_adj   = max(PROG_TRAIL_VOL_MIN, min(PROG_TRAIL_VOL_MAX, vol_ratio))

    result = base * vol_adj

    # ATR-aware floor: never trail tighter than 0.8×ATR (avoids wick shakeouts)
    atr_floor = atr_pct * 0.8
    result = max(result, atr_floor)

    # Final clamp
    if strategy == "SCALPER":
        result = max(SCALPER_TRAIL_MIN, min(SCALPER_TRAIL_MAX, result))
    else:
        result = max(f * 0.8, min(c * 1.2, result))

    return round(result, 5)

def ws_price(symbol: str) -> float | None:
    with _ws_lock:
        entry = _live_prices.get(symbol)
    if entry is None:
        return None
    price, updated_at = entry
    if time.time() - updated_at > WS_STALE_SECS:
        return None
    return price

async def _ws_loop():
    try:
        import websockets
    except ImportError:
        log.error("🔌 'websockets' library not installed — WS monitor disabled.")
        return
    backoff = 2
    last_wanted = set()
    while True:
        wanted = {t["symbol"] for t in list(scalper_trades) + list(alt_trades)}
        if not wanted:
            await asyncio.sleep(5)
            continue
        try:
            async with websockets.connect(
                WS_URL, ping_interval=None, close_timeout=5, open_timeout=10,
            ) as ws:
                log.info("🔌 WS price monitor connected")
                backoff = 2
                subscribed = set()
                last_ping = time.time()
                while True:
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
                    if time.time() - last_ping >= WS_PING_SECS:
                        await ws.send(json.dumps({"method": "PING"}))
                        last_ping = time.time()
                    try:
                        raw = await asyncio.wait_for(ws.recv(), timeout=0.5)
                    except asyncio.TimeoutError:
                        continue
                    if isinstance(raw, bytes):
                        continue
                    try:
                        msg = json.loads(raw)
                    except Exception:
                        continue
                    d = msg.get("d", {})
                    sym = msg.get("s") or d.get("s")
                    px = d.get("p")
                    if sym and px:
                        with _ws_lock:
                            _live_prices[sym] = (float(px), time.time())
        except Exception as e:
            log.warning(f"🔌 WS error ({type(e).__name__}: {e}) — reconnect in {backoff}s")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 60)

def _start_ws_monitor():
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

# ── State persistence (unchanged) ───────────────────────────
def save_state():
    try:
        payload = {
            "scalper_trades":       scalper_trades,
            "alt_trades":           alt_trades,
            "trade_history":        trade_history,
            "consecutive_losses":   _consecutive_losses,
            "win_rate_pause_until": _win_rate_pause_until,
            "streak_paused_at":     _streak_paused_at,
            "paused":               _paused,
            "scalper_excluded":     _scalper_excluded,
            "alt_excluded":         list(_alt_excluded),
            "api_blacklist":        list(_api_blacklist),
            "liquidity_blacklist":  _liquidity_blacklist,
            "liquidity_fail_count": _liquidity_fail_count,
            "adaptive_offsets":       _adaptive_offsets,
            "last_rebalance_count":   _last_rebalance_count,
            "dynamic_scalper_budget": _dynamic_scalper_budget,
            "dynamic_moonshot_budget":_dynamic_moonshot_budget,
            "saved_at":             datetime.now(timezone.utc).isoformat(),
        }
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(payload, f, default=str)
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        log.warning(f"State save failed: {e}")

def load_state() -> tuple:
    defaults = ([], [], [], 0, 0.0, 0.0, False, {}, set(), set(), {}, {},
                {"SCALPER": 0.0, "MOONSHOT": 0.0}, 0, None, None)
    try:
        if not os.path.exists(STATE_FILE):
            return defaults
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
            d.get("paused",               False),
            d.get("scalper_excluded",     {}),
            set(d.get("alt_excluded",     [])),
            set(d.get("api_blacklist",    [])),
            d.get("liquidity_blacklist",  {}),
            d.get("liquidity_fail_count", {}),
            d.get("adaptive_offsets",       {"SCALPER": 0.0, "MOONSHOT": 0.0}),
            d.get("last_rebalance_count",   0),
            d.get("dynamic_scalper_budget", None),
            d.get("dynamic_moonshot_budget",None),
        )
    except Exception as e:
        log.warning(f"State load failed ({e}) — starting fresh")
        return defaults

def _get_session() -> requests.Session:
    if not hasattr(_thread_local, "session"):
        s = requests.Session()
        s.headers.update({"Accept": "application/json"})
        _thread_local.session = s
    return _thread_local.session

# ── Telegram (unchanged) ────────────────────────────────────
def telegram(msg: str, parse_mode: str = "HTML"):
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
                log.debug("Telegram HTML parse error — retrying as plain text")
                r2 = _get_session().post(
                    url,
                    json={"chat_id": TELEGRAM_CHAT_ID, "text": re.sub(r'<[^>]+>', '', msg), "parse_mode": ""},
                    timeout=8,
                )
                if r2.ok:
                    return
                log.warning(f"Telegram plain-text fallback also failed: {r2.text[:100]}")
                return
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

# ── Sentiment / AI (unchanged) ───────────────────────────────
def get_sentiment(symbol: str) -> tuple[float | None, str]:
    if not SENTIMENT_ENABLED or not WEB_SEARCH_ENABLED:
        return None, ""
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
        text = ""
        for block in data.get("content", []):
            if block.get("type") == "text":
                text = block["text"].strip()
                break
        if not text:
            return None, ""
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
        score   = max(-1.0, min(1.0, score))
        with _sentiment_lock:
            _sentiment_cache[symbol] = (score, summary, time.time())
        log.info(f"🧠 Sentiment [{coin}]: {score:+.2f} — {summary}")
        return score, summary
    except Exception as e:
        log.debug(f"🧠 Sentiment fetch failed for {coin}: {e}")
        return None, ""

def sentiment_score_adjustment(symbol: str) -> tuple[float, str]:
    score, summary = get_sentiment(symbol)
    if score is None:
        return 0.0, ""
    if score >= 0:
        delta = round(score * SENTIMENT_MAX_BONUS,   1)
        label = f"🟢 sentiment {score:+.2f} (+{delta:.0f}pts)"
    else:
        delta = round(score * SENTIMENT_MAX_PENALTY, 1)
        label = f"🔴 sentiment {score:+.2f} ({delta:+.0f}pts)"
    return delta, label

def get_trending_coins() -> list[tuple[str, str]]:
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
        parsed = None
        try:
            parsed = json.loads(text)
        except json.JSONDecodeError:
            depth, start = 0, -1
            for i, ch in enumerate(text):
                if ch == "{":
                    if depth == 0:
                        start = i
                    depth += 1
                elif ch == "}" and depth > 0:
                    depth -= 1
                    if depth == 0 and start >= 0:
                        try:
                            parsed = json.loads(text[start:i + 1])
                        except json.JSONDecodeError:
                            pass
                        break
        if parsed is None:
            return _trending_coins
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
    with _moonshot_scan_sem:
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

def check_dead_coin(symbol: str, vol_24h: float, spread: float,
                    strategy: str = "SCALPER") -> bool:
    global _liquidity_blacklist, _liquidity_fail_count
    until_ts = _liquidity_blacklist.get(symbol)
    if until_ts:
        if time.time() < until_ts:
            return True
        else:
            del _liquidity_blacklist[symbol]
            _liquidity_fail_count.pop(symbol, None)
            log.info(f"💧 [DEAD_COIN] {symbol} blacklist expired — re-enabled")
    vol_threshold = (DEAD_COIN_VOL_SCALPER if strategy == "SCALPER"
                     else DEAD_COIN_VOL_MOONSHOT)
    failed = (vol_24h < vol_threshold) or (spread > DEAD_COIN_SPREAD_MAX)
    if failed:
        count = _liquidity_fail_count.get(symbol, 0) + 1
        _liquidity_fail_count[symbol] = count
        log.debug(f"💧 [DEAD_COIN] {symbol} fail #{count}/{DEAD_COIN_CONSECUTIVE} "
                  f"(vol=${vol_24h:,.0f} spread={spread*100:.3f}%)")
        if count >= DEAD_COIN_CONSECUTIVE:
            until_ts = time.time() + DEAD_COIN_BLACKLIST_HOURS * 3600
            _liquidity_blacklist[symbol] = until_ts
            _liquidity_fail_count.pop(symbol, None)
            log.info(f"☠️  [DEAD_COIN] {symbol} blacklisted for {DEAD_COIN_BLACKLIST_HOURS}h "
                     f"(vol=${vol_24h:,.0f} spread={spread*100:.3f}%)")
            save_state()
        return True
    else:
        _liquidity_fail_count.pop(symbol, None)
        return False

def keltner_breakout(df: pd.DataFrame, atr_mult: float = None) -> bool:
    if atr_mult is None:
        atr_mult = KELTNER_ATR_MULT
    try:
        if df is None or len(df) < 20:
            return False
        close = df["close"]
        high  = df["high"]
        low   = df["low"]
        hl2   = (high + low) / 2
        atr   = calc_atr(df, period=14)
        upper = float(hl2.iloc[-1]) + atr_mult * atr
        return float(close.iloc[-1]) > upper
    except Exception:
        return False

def public_get(path, params=None):
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
                    telegram(f"⚠️ <b>MEXC API down</b> | {_api_fail_count} failures | retrying")
                time.sleep(sleep_secs)
                raise
    raise requests.RequestException(f"GET {path} failed after {HTTP_RETRIES} attempts")

def _sign_request(params: dict, path: str) -> tuple[str, dict]:
    p         = {**params, "timestamp": int(time.time() * 1000)}
    qs        = urllib.parse.urlencode(p)
    signature = hmac.new(MEXC_API_SECRET.encode(), qs.encode(), hashlib.sha256).hexdigest()
    url       = f"{BASE_URL}{path}?{qs}&signature={signature}"
    headers   = {"X-MEXC-APIKEY": MEXC_API_KEY}
    return url, headers

def private_request(method, path, params=None):
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
    d_price = Decimal(str(price))
    d_tick  = Decimal(str(tick_size))
    rounded = (d_price / d_tick).to_integral_value(rounding=ROUND_DOWN) * d_tick
    decimals = max(0, -rounded.normalize().as_tuple().exponent)
    return round(float(rounded), decimals)

def calc_qty(budget: float, price: float, step_size: float) -> float:
    if price <= 0 or step_size <= 0:
        return 0.0
    d_budget = Decimal(str(budget))
    d_price  = Decimal(str(price))
    d_step   = Decimal(str(step_size))
    raw      = d_budget / d_price
    floored  = (raw / d_step).to_integral_value(rounding=ROUND_DOWN) * d_step
    return float(floored)

def get_available_balance() -> float:
    if PAPER_TRADE:
        return round(PAPER_BALANCE + sum(t["pnl_usdt"] for t in trade_history), 2)
    try:
        data = private_get("/api/v3/account")
        for b in data.get("balances", []):
            if b["asset"] == "USDT":
                return float(b["free"])   # only free USDT is available for new trades
        return 0.0
    except Exception as e:
        log.error(f"Balance fetch failed: {e}")
        return 0.0

def get_asset_balance(symbol: str) -> float:
    """Return total (free + locked) balance of the base asset."""
    if PAPER_TRADE:
        # For paper trading, just return the qty from the trade state
        for t in scalper_trades + alt_trades:
            if t["symbol"] == symbol:
                return t["qty"]
        return 0.0
    try:
        asset = symbol.replace("USDT", "")
        data = private_get("/api/v3/account")
        for b in data.get("balances", []):
            if b["asset"] == asset:
                return float(b.get("free", 0)) + float(b.get("locked", 0))
        return 0.0
    except Exception as e:
        log.error(f"Failed to fetch balance for {symbol}: {e}")
        return 0.0

def get_sellable_qty(symbol: str, fallback_qty: float = 0.0) -> float:
    """
    Fetch the actual on-exchange balance and round it to the symbol's step_size.
    This prevents "quantity scale is invalid" errors from stale or imprecise qty values.
    Returns 0.0 if the position is too small to sell.
    """
    actual = get_asset_balance(symbol)
    if actual <= 0:
        return 0.0
    min_qty, step_size, min_notional, _ = get_symbol_rules(symbol)
    # Round down to step_size
    d_actual = Decimal(str(actual))
    d_step   = Decimal(str(step_size))
    rounded  = float((d_actual / d_step).to_integral_value(rounding=ROUND_DOWN) * d_step)
    if rounded < min_qty:
        log.debug(f"[SELL_QTY] {symbol}: actual {actual:.8f} → rounded {rounded:.8f} < min {min_qty}")
        return 0.0
    return rounded

def calc_rsi(series, period=14) -> float:
    delta = series.diff()
    gain  = delta.clip(lower=0).ewm(alpha=1.0 / period, adjust=False).mean()
    loss  = (-delta.clip(upper=0)).ewm(alpha=1.0 / period, adjust=False).mean()
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
    atr = tr.ewm(alpha=1.0 / period, adjust=False).mean().iloc[-1]
    return float(atr) if not np.isnan(atr) else 0.0

def calc_vol_zscore(volume: pd.Series, lookback: int = 20) -> float:
    try:
        if len(volume) < lookback + 1:
            return 0.0
        window  = volume.iloc[-(lookback + 1):-1]
        current = float(volume.iloc[-1])
        mean    = float(window.mean())
        std     = float(window.std())
        if std <= 0 or mean <= 0:
            return 0.0
        return (current - mean) / std
    except Exception:
        return 0.0

def calc_move_maturity(df: pd.DataFrame, lookback: int = None) -> float:
    if lookback is None:
        lookback = MATURITY_LOOKBACK
    try:
        if df is None or len(df) < lookback:
            return 0.5
        window  = df.iloc[-lookback:]
        high    = float(window["high"].max())
        low     = float(window["low"].min())
        current = float(df["close"].iloc[-1])
        if high <= low:
            return 0.5
        return max(0.0, min(1.0, (current - low) / (high - low)))
    except Exception:
        return 0.5

def maturity_penalty(maturity: float, raw_score: float,
                     threshold: float = None) -> float:
    if threshold is None:
        threshold = MATURITY_THRESHOLD
    if maturity <= threshold:
        return 0.0
    overshoot = (maturity - threshold) / (1.0 - threshold) if threshold < 1.0 else 0.0
    penalty = raw_score * MATURITY_PENALTY_MULT * overshoot
    return round(penalty, 1)

def detect_momentum_decay(symbol: str, min_candles: int = None,
                          price_range: float = None) -> bool:
    if min_candles is None:
        min_candles = MOMENTUM_DECAY_CANDLES
    if price_range is None:
        price_range = MOMENTUM_DECAY_PRICE_RANGE
    try:
        needed = max(min_candles + 2, 8)
        df = parse_klines(symbol, interval="5m", limit=needed + 5, min_len=needed)
        if df is None:
            return False
        vol   = df["volume"].iloc[-(min_candles + 1):]
        close = df["close"].iloc[-min_candles:]
        vol_vals = vol.values
        declining = all(
            float(vol_vals[i + 1]) < float(vol_vals[i])
            for i in range(len(vol_vals) - 1)
        )
        if not declining:
            return False
        close_vals  = [float(c) for c in close.values]
        price_high  = max(close_vals)
        price_low   = min(close_vals)
        mid         = (price_high + price_low) / 2 if (price_high + price_low) > 0 else 1.0
        flat_range  = (price_high - price_low) / mid
        if flat_range >= price_range:
            return False
        log.info(f"📉 [MOMENTUM_DECAY] {symbol} — vol declining {min_candles} candles, "
                 f"price range {flat_range*100:.3f}%")
        return True
    except Exception:
        return False

def update_adaptive_thresholds():
    """
    Adjust entry thresholds based on recent performance.
    
    Key safeguards against noise-chasing:
    - Requires minimum 10 trades (not 5) for any adjustment
    - Uses win-rate + expectancy instead of raw Sharpe (more stable on small samples)
    - Mean-reverts: offsets decay toward 0 on every evaluation (prevents runaway tightening)
    - Symmetric step sizes: tighten and relax at the same rate
    - Confidence gate: only adjusts when signal is clear (not borderline)
    """
    global _adaptive_offsets
    DECAY_RATE = 0.15  # offset decays 15% toward 0 on each evaluation
    MIN_TRADES_FOR_ADJUST = max(10, ADAPTIVE_WINDOW // 2)
    
    for strategy in ("SCALPER", "MOONSHOT"):
        full = [t for t in trade_history
                if t.get("label") == strategy
                and not t.get("is_partial")][-ADAPTIVE_WINDOW:]
        if len(full) < MIN_TRADES_FOR_ADJUST:
            continue
        
        pnls = [t["pnl_pct"] for t in full]
        n    = len(pnls)
        wins = sum(1 for p in pnls if p > 0)
        win_rate = wins / n
        mean_pnl = sum(pnls) / n
        
        old_offset = _adaptive_offsets.get(strategy, 0.0)
        
        # Step 1: Decay toward neutral (mean reversion)
        decayed_offset = old_offset * (1 - DECAY_RATE)
        
        # Step 2: Only adjust if signal is CLEARLY bad or clearly good
        # Bad: win rate < 35% AND negative expectancy (both must agree)
        # Good: win rate > 55% AND positive expectancy
        # Everything else: just decay, don't adjust
        if win_rate < 0.35 and mean_pnl < 0:
            new_offset = min(decayed_offset + ADAPTIVE_TIGHTEN_STEP, ADAPTIVE_MAX_OFFSET)
            direction  = "tightened"
        elif win_rate > 0.55 and mean_pnl > 0:
            new_offset = max(decayed_offset - ADAPTIVE_RELAX_STEP, ADAPTIVE_MIN_OFFSET)
            direction  = "relaxed"
        else:
            new_offset = decayed_offset
            direction  = "decayed" if abs(decayed_offset - old_offset) > 0.1 else "unchanged"
        
        # Round to avoid floating point drift
        new_offset = round(new_offset, 1)
        
        if abs(new_offset - old_offset) > 0.05:
            _adaptive_offsets[strategy] = new_offset
            signal_stats = _compute_signal_stats(full)
            signal_summary = " | ".join(
                f"{sig}:{s['wins']}W/{s['total']-s['wins']}L"
                for sig, s in sorted(signal_stats.items())
                if s["total"] >= 2
            )
            log.info(f"🧠 [ADAPTIVE] {strategy} threshold {direction}: "
                     f"offset {old_offset:+.1f} → {new_offset:+.1f} "
                     f"(WR={win_rate*100:.0f}% avg={mean_pnl:+.2f}% over {n} trades)"
                     + (f" [{signal_summary}]" if signal_summary else ""))

def _compute_signal_stats(trades: list) -> dict:
    by_signal: dict = {}
    for t in trades:
        sig = t.get("entry_signal", "UNKNOWN")
        if sig not in by_signal:
            by_signal[sig] = {"total": 0, "wins": 0, "losses": 0,
                              "pnl_sum": 0.0, "pnl_list": []}
        by_signal[sig]["total"] += 1
        by_signal[sig]["pnl_sum"] += t.get("pnl_pct", 0)
        by_signal[sig]["pnl_list"].append(t.get("pnl_pct", 0))
        if t.get("pnl_pct", 0) > 0:
            by_signal[sig]["wins"] += 1
        else:
            by_signal[sig]["losses"] += 1
    for sig, s in by_signal.items():
        s["avg_pnl"]  = round(s["pnl_sum"] / s["total"], 2) if s["total"] > 0 else 0.0
        s["win_rate"] = round(s["wins"] / s["total"] * 100, 1) if s["total"] > 0 else 0.0
        del s["pnl_list"]
    return by_signal

def get_effective_threshold(strategy: str) -> float:
    base = {"SCALPER": SCALPER_THRESHOLD, "MOONSHOT": MOONSHOT_MIN_SCORE}.get(strategy, 40)
    offset = _adaptive_offsets.get(strategy, 0.0)
    return base + offset

def get_regime_multiplier() -> float:
    """Return a multiplier to adjust entry thresholds based on BTC market regime."""
    return _market_regime_mult

def rebalance_budgets():
    """
    Shift per-trade budget between scalper and moonshot based on performance.
    
    Key safeguards:
    - Requires 15+ trades per strategy (not 5) before comparing
    - Uses win rate × expectancy product instead of raw Sharpe (more stable)
    - Mean-reverts toward defaults when signal is unclear
    - Smaller shift steps to avoid overreaction
    """
    global _last_rebalance_count, _dynamic_scalper_budget, _dynamic_moonshot_budget
    full = [t for t in trade_history if not t.get("is_partial")]
    if len(full) < PERF_REBALANCE_TRADES or len(full) <= _last_rebalance_count:
        return
    if len(full) - _last_rebalance_count < PERF_REBALANCE_TRADES:
        return
    _last_rebalance_count = len(full)
    
    MIN_STRATEGY_TRADES = 15  # need real sample, not 5
    
    def strategy_score(label: str) -> float | None:
        """Return a performance score combining win rate and expectancy.
        Returns None if insufficient data."""
        st = [t for t in full if t.get("label") == label][-PERF_REBALANCE_TRADES:]
        if len(st) < MIN_STRATEGY_TRADES:
            return None
        pnls = [t["pnl_pct"] for t in st]
        wins = sum(1 for p in pnls if p > 0)
        wr   = wins / len(pnls)
        mean = sum(pnls) / len(pnls)
        # Score = win_rate × sign(mean) × |mean|^0.5
        # This is more stable than Sharpe on small samples because it
        # doesn't divide by std (which is noisy on <20 samples)
        return wr * (1 if mean >= 0 else -1) * (abs(mean) ** 0.5)
    
    scalper_score  = strategy_score("SCALPER")
    moonshot_score = strategy_score("MOONSHOT")
    
    # If either has insufficient data, don't rebalance
    if scalper_score is None or moonshot_score is None:
        return
    
    curr_scalper  = _dynamic_scalper_budget  or SCALPER_BUDGET_PCT
    curr_moonshot = _dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT
    
    # Mean-revert toward defaults (prevents runaway shifts)
    REVERT_RATE = 0.10
    curr_scalper  = curr_scalper  + (SCALPER_BUDGET_PCT  - curr_scalper)  * REVERT_RATE
    curr_moonshot = curr_moonshot + (MOONSHOT_BUDGET_PCT - curr_moonshot) * REVERT_RATE
    
    # Only shift if the difference in scores is large and clear
    diff = scalper_score - moonshot_score
    shift = PERF_SHIFT_STEP * 0.5  # halved from original — smaller steps
    
    if diff > 0.3:  # scalper clearly better
        new_scalper  = min(PERF_SCALPER_CEIL,  curr_scalper  + shift)
        new_moonshot = max(PERF_MOONSHOT_FLOOR, curr_moonshot - shift)
    elif diff < -0.3:  # moonshot clearly better
        new_scalper  = max(PERF_SCALPER_FLOOR,  curr_scalper  - shift)
        new_moonshot = min(PERF_MOONSHOT_CEIL,  curr_moonshot + shift)
    else:
        new_scalper  = curr_scalper
        new_moonshot = curr_moonshot
    
    new_scalper  = round(new_scalper, 4)
    new_moonshot = round(new_moonshot, 4)
    
    if abs(new_scalper - (_dynamic_scalper_budget or SCALPER_BUDGET_PCT)) > 0.001 or \
       abs(new_moonshot - (_dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT)) > 0.001:
        _dynamic_scalper_budget  = new_scalper
        _dynamic_moonshot_budget = new_moonshot
        log.info(f"💼 [REBALANCE] Scalper: {new_scalper*100:.1f}% "
                 f"(score {scalper_score:.2f}) | "
                 f"Moonshot: {new_moonshot*100:.1f}% "
                 f"(score {moonshot_score:.2f})")
        telegram(
            f"💼 <b>Budget Rebalanced</b>\n"
            f"🟢 S {new_scalper*100:.1f}% ({scalper_score:+.2f}) | "
            f"🌙 M {new_moonshot*100:.1f}% ({moonshot_score:+.2f})"
        )

def get_effective_budget_pct(strategy: str) -> float:
    if strategy == "SCALPER":
        return _dynamic_scalper_budget or SCALPER_BUDGET_PCT
    elif strategy == "MOONSHOT":
        return _dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT
    return SCALPER_BUDGET_PCT

def calc_fee_aware_tp_floor() -> float:
    recent = [t for t in trade_history if t.get("fee_usdt", 0) > 0][-25:]
    if len(recent) < 6:
        return 0.0018 + FEE_SLIPPAGE_BUFFER + 0.0105
    avg_fee = sum(t["fee_usdt"] / t["cost_usdt"] for t in recent if t.get("cost_usdt", 0) > 0) / len(recent)
    return round(avg_fee + FEE_SLIPPAGE_BUFFER + 0.010, 4)

def classify_entry_signal(crossed_now: bool = False, vol_ratio: float = 1.0,
                          rsi: float = 50.0, is_new: bool = False,
                          is_trending: bool = False,
                          label: str = "SCALPER") -> str:
    if label in ("REVERSAL",):
        return "CAPITULATION_BOUNCE"
    if label in ("TRINITY",):
        return "DEEP_DIP_RECOVERY"
    if crossed_now:
        return "CROSSOVER"
    if vol_ratio >= 3.0:
        return "VOL_SPIKE"
    if rsi < 40:
        return "OVERSOLD"
    if is_trending:
        return "TRENDING"
    if is_new:
        return "NEW_LISTING"
    return "TREND"

_SIGNAL_TP_MULT = {
    "CROSSOVER":  SCALPER_TP_MULT_CROSSOVER,
    "VOL_SPIKE":  SCALPER_TP_MULT_VOL_SPIKE,
    "OVERSOLD":   SCALPER_TP_MULT_OVERSOLD,
    "TREND":      SCALPER_TP_MULT_DEFAULT,
    "TRENDING":   SCALPER_TP_MULT_DEFAULT,
    "NEW_LISTING":SCALPER_TP_MULT_DEFAULT,
}
_SIGNAL_SL_MULT = {
    "VOL_SPIKE":  SCALPER_SL_MULT_VOL_SPIKE,
    "OVERSOLD":   SCALPER_SL_MULT_OVERSOLD,
}

def parse_klines(symbol, interval="5m", limit=60, min_len=30) -> pd.DataFrame | None:
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
        if len(_kline_cache) >= MAX_KLINE_CACHE:
            now        = time.time()
            stale_keys = [k for k, (_, t) in _kline_cache.items()
                          if now - t > KLINE_CACHE_TTL]
            for k in stale_keys:
                del _kline_cache[k]
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

def get_btc_pulse_ratio() -> float:
    try:
        df_1h = parse_klines("BTCUSDT", interval="1h", limit=25, min_len=24)
        if df_1h is None or len(df_1h) < 25:
            return 1.0
        volumes = df_1h["volume"].values
        current_1h = float(volumes[-1])
        avg_24h = float(np.mean(volumes[-24:]))
        if avg_24h == 0:
            return 1.0
        ratio = current_1h / avg_24h
        return max(0.3, min(2.0, ratio))
    except Exception:
        return 1.0

def _score_scalper(sym: str, strict: bool = False, btc_pulse_ratio: float = 1.0) -> dict | None:
    df_1h = parse_klines(sym, interval="60m", limit=60)
    if df_1h is None:
        return None
    ema50_1h  = calc_ema(df_1h["close"], 50).iloc[-1]
    ema50_gap = (float(df_1h["close"].iloc[-1]) / float(ema50_1h) - 1)
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

    if strict and not crossed_now and vol_ratio < 3.0 and rsi >= 40:
        if rsi_delta < 1.0:
            log.debug(f"[SCALPER] Skip {sym} — TREND signal with declining RSI "
                      f"(delta {rsi_delta:+.1f})")
            return None

    confluence_bonus = (SCALPER_CONFLUENCE_BONUS
                        if crossed_now and vol_ratio > 2.0 and rsi_delta > 0
                        else 0.0)

    score          = rsi_score + ma_score + vol_score + confluence_bonus - ema50_penalty

    move_mat = calc_move_maturity(df5m, MATURITY_LOOKBACK)
    mat_pen  = maturity_penalty(move_mat, max(score, 1.0), MATURITY_THRESHOLD)
    score    = score - mat_pen

    # Apply market regime multiplier only for strict scoring (entry)
    regime_mult = get_regime_multiplier() if strict else 1.0
    eff_threshold = get_effective_threshold("SCALPER") * regime_mult if strict else max(5, SCALPER_THRESHOLD // 2)

    if score < eff_threshold:
        if mat_pen > 0:
            log.debug(f"[SCALPER] Skip {sym} — maturity {move_mat:.2f} penalty -{mat_pen:.1f}pts")
        elif ema50_penalty > 0:
            log.debug(f"[SCALPER] Skip {sym} — EMA50 penalty {ema50_penalty:.1f}pts "
                      f"({ema50_gap*100:.1f}% below EMA50)")
        return None

    sentiment_delta = 0.0
    if strict:
        dynamic_vol_threshold = SCALPER_MIN_1H_VOL * btc_pulse_ratio
        recent_vol_usdt = float(volume.iloc[-12:].sum()) * float(close.iloc[-1])
        if recent_vol_usdt < dynamic_vol_threshold:
            log.debug(f"[SCALPER] Skip {sym} — thin "
                      f"(1h vol ${recent_vol_usdt:,.0f} < ${dynamic_vol_threshold:,.0f} "
                      f"pulse={btc_pulse_ratio:.2f})")
            return None
        if btc_pulse_ratio < 0.8:
            score += 5
            log.debug(f"[SCALPER] {sym} quiet market bonus +5 (pulse {btc_pulse_ratio:.2f})")
        elif btc_pulse_ratio > 1.5:
            score -= 5
            log.debug(f"[SCALPER] {sym} frenzied market penalty -5 (pulse {btc_pulse_ratio:.2f})")

        eff_thresh = get_effective_threshold("SCALPER") * regime_mult
        if (score >= eff_thresh - SENTIMENT_MAX_BONUS
                and score <= eff_thresh + SENTIMENT_MAX_PENALTY):
            sentiment_delta, sentiment_label = sentiment_score_adjustment(sym)
            score = round(score + sentiment_delta, 2)
            if sentiment_delta != 0:
                log.info(f"[SCALPER] {sym} sentiment: {sentiment_label} → score {score}")
        if score < eff_thresh:
            log.info(f"[SCALPER] Skip {sym} — below threshold after sentiment ({score:.1f})")
            return None

    atr     = calc_atr(df5m, period=SCALPER_ATR_PERIOD)
    atr_pct = atr / float(close.iloc[-1]) if float(close.iloc[-1]) > 0 else 0.015

    if strict and atr_pct < SCALPER_MIN_ATR_PCT:
        log.debug(f"[SCALPER] Skip {sym} — low volatility "
                  f"(ATR {atr_pct*100:.3f}% < {SCALPER_MIN_ATR_PCT*100:.1f}%)")
        return None

    keltner_bonus = 0.0
    if strict and KELTNER_SCORE_BONUS > 0:
        df_15m = parse_klines(sym, interval="15m", limit=40, min_len=20)
        if keltner_breakout(df_15m):
            keltner_bonus = KELTNER_SCORE_BONUS
            log.debug(f"[SCALPER] {sym} Keltner breakout confirmed (+{keltner_bonus:.0f}pts)")

    score = round(score + keltner_bonus, 2)

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
        "keltner_bonus":   keltner_bonus,
        "vol_ratio":       round(vol_ratio, 2),
        "ema50_gap":       round(ema50_gap * 100, 2),
        "ema50_penalty":   ema50_penalty,
        "move_maturity":   round(move_mat, 3),
        "maturity_penalty":mat_pen,
        "entry_signal":    classify_entry_signal(crossed_now=crossed_now,
                                                  vol_ratio=vol_ratio, rsi=rsi),
        "price":           curr_close,
        "atr_pct":         round(atr_pct, 6),
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
    global _watchlist, _watchlist_at
    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= SCALPER_MIN_PRICE]
    df = df[df["abs_change"]  >= SCALPER_MIN_CHANGE]
    df = df[~df["symbol"].isin(_api_blacklist)]
    now_ts = time.time()
    df = df[~df["symbol"].apply(lambda s: _liquidity_blacklist.get(s, 0) > now_ts)]

    by_vol    = df.sort_values("quoteVolume", ascending=False).head(100)["symbol"].tolist()
    by_change = df.sort_values("abs_change",  ascending=False).head(WATCHLIST_SURGE_SIZE)["symbol"].tolist()
    candidates = list(dict.fromkeys(by_change + by_vol))

    new_listing_syms = {n["symbol"] for n in _new_listings_cache}
    established = [s for s in candidates if s not in new_listing_syms]
    log.info(f"📋 [WATCHLIST] {len(established)} established pairs after age filter "
             f"({len(candidates) - len(established)} new listings excluded)")

    ticker_vol = dict(zip(tickers["symbol"], tickers["quoteVolume"].fillna(0)))

    btc_pulse = get_btc_pulse_ratio()
    scores = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        futures = {ex.submit(_score_scalper, sym, False, btc_pulse): sym for sym in established}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result and result["score"] >= WATCHLIST_MIN_SCORE:
                    vol_24h = ticker_vol.get(result["symbol"], 0)
                    if not check_dead_coin(result["symbol"], vol_24h, 0.0, "SCALPER"):
                        scores.append(result)
            except Exception as e:
                sym = futures[f]
                log.debug(f"[WATCHLIST] Score failed for {sym}: {e}")

    scores.sort(key=lambda x: x["score"], reverse=True)
    _watchlist    = scores[:WATCHLIST_SIZE]
    _watchlist_at = time.time()

    if not _watchlist:
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

    why_not = []
    if _paused:
        why_not.append("bot paused")
    if len(scalper_trades) >= SCALPER_MAX_TRADES:
        why_not.append(f"at max {SCALPER_MAX_TRADES} trades")
    if top["score"] < SCALPER_THRESHOLD:
        why_not.append(f"score {top['score']:.0f} < threshold {SCALPER_THRESHOLD}")
    if _btc_ema_gap < -0.005:
        penalty = round(abs(_btc_ema_gap) * BTC_REGIME_EMA_PENALTY, 1)
        why_not.append(f"BTC {_btc_ema_gap*100:.1f}% below EMA (-{penalty:.0f}pts penalty)")
    if top.get("ema50_penalty", 0) > 0:
        why_not.append(f"coin EMA50 -{top['ema50_penalty']:.0f}pts ({top['ema50_gap']:.1f}% below)")
    status_line = f"Holding off: {', '.join(why_not)}" if why_not else "Ready to enter ✅"

    telegram(
        f"📋 <b>Watchlist</b> | {len(symbols)} pairs\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Top: <b>{top_line}</b>\n"
        f"{status_line}"
    )

def find_scalper_opportunity(budget: float, exclude: dict, open_symbols: set) -> dict | None:
    global last_top_scalper
    if not _watchlist:
        log.info("🔍 [SCALPER] Watchlist empty — skipping until next rebuild.")
        return None
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

    btc_pulse = get_btc_pulse_ratio()
    refreshed = []
    for s in candidates[:5]:
        result = _score_scalper(s["symbol"], strict=True, btc_pulse_ratio=btc_pulse)
        if result:
            refreshed.append(result)
        time.sleep(0.05)

    if not refreshed:
        log.info("🔍 [SCALPER] All re-scores returned None — skipping entry this cycle.")
        return None

    refreshed.sort(key=lambda x: x["score"], reverse=True)
    best = refreshed[0]
    last_top_scalper = best

    age_mins = (time.time() - _watchlist_at) / 60
    scanner_log(f"📊 [SCALPER] Top: {best['symbol']} | Score: {best['score']}/100 | "
                f"Signal: {best.get('entry_signal','?')} | "
                f"RSI: {best['rsi']} | ATR: {best['atr_pct']*100:.2f}% | "
                f"watchlist age: {age_mins:.0f}min")

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
                filtered.append(cand)
        refreshed = filtered if filtered else refreshed

    return pick_tradeable(refreshed, budget, "SCALPER")

def find_new_listings(tickers: pd.DataFrame, exclude: set, open_symbols: set) -> list:
    global _new_listings_cache, _new_listings_cache_at
    if time.time() - _new_listings_cache_at < NEW_LISTINGS_CACHE_TTL:
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
        except Exception:
            pass
        time.sleep(0.05)
    _new_listings_cache    = new
    _new_listings_cache_at = time.time()
    log.info(f"🌙 [MOONSHOT] {len(new)} new listings ({MOONSHOT_MIN_DAYS}-{MOONSHOT_NEW_DAYS} days) — cached for {NEW_LISTINGS_CACHE_TTL}s")
    return [n for n in new if n["symbol"] not in open_symbols and n["symbol"] not in exclude]

def find_moonshot_opportunity(tickers: pd.DataFrame, budget: float,
                               balance: float,
                               exclude: set, open_symbols: set) -> dict | None:
    global last_top_alt
    min_1h_vol = max(5_000, balance * MOONSHOT_LIQUIDITY_RATIO)
    max_vol    = max(5_000_000, balance * MOONSHOT_MAX_VOL_RATIO)
    log.debug(f"🌙 [MOONSHOT] Vol window: ${min_1h_vol:,.0f}/hr – ${max_vol:,.0f}/day "
              f"(balance ${balance:.0f})")
    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"] <= max_vol]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    momentum_candidates = (df[df["priceChangePercent"] > 0]  # only positive momentum for longs
                             .sort_values("priceChangePercent", ascending=False)
                             .head(40)["symbol"].tolist())
    new_listings = find_new_listings(tickers, exclude=exclude, open_symbols=open_symbols)
    new_symbols  = [n["symbol"] for n in new_listings]
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
    ticker_vol_map    = dict(zip(df["symbol"], df["quoteVolume"].fillna(0)))
    ticker_change_map = dict(zip(df["symbol"], df["priceChangePercent"].fillna(0)))

    def _score_moonshot(sym: str) -> dict | None:
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
        rsi_prev  = calc_rsi(close.iloc[:-1])
        rsi_delta = rsi - rsi_prev if not np.isnan(rsi_prev) else 0.0
        avg_vol   = float(volume.iloc[-20:-1].mean()) if len(volume) >= 21 else 0.0
        vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0
        is_rebound_context = (
            rsi_delta  >= MOONSHOT_REBOUND_RSI_DELTA
            and vol_ratio >= MOONSHOT_REBOUND_VOL_RATIO
            and rsi <= MOONSHOT_REBOUND_MAX_RSI
        )
        effective_max_rsi = MOONSHOT_REBOUND_MAX_RSI if is_rebound_context else MOONSHOT_MAX_RSI
        if rsi > effective_max_rsi:
            return None
        if rsi < MOONSHOT_MIN_RSI:
            return None
        if is_rebound_context and rsi > MOONSHOT_MAX_RSI:
            log.debug(f"[MOONSHOT] {sym} rebound RSI gate: {rsi:.1f} allowed "
                      f"(delta={rsi_delta:+.1f} vol={vol_ratio:.1f}× — rebound context)")
        if rsi > MOONSHOT_RSI_ACCEL_MIN and rsi_delta < MOONSHOT_RSI_ACCEL_DELTA:
            return None
        rsi_score = max(0, 40 - rsi) if rsi < 50 else 0
        ema9  = calc_ema(close, 9)
        ema21 = calc_ema(close, 21)
        crossed   = (ema9.iloc[-1] > ema21.iloc[-1]) and (ema9.iloc[-2] <= ema21.iloc[-2])
        ma_score  = 30 if crossed else 0
        vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
        if vol_ratio < MOONSHOT_MIN_VOL_RATIO:
            return None
        recent_candles = 1 if is_new else 4
        recent_1h_vol = float(volume.iloc[-recent_candles:].sum()) * float(close.iloc[-1])
        if recent_1h_vol < min_1h_vol:
            log.debug(f"[MOONSHOT] Skip {sym} — dead recently "
                      f"(1h vol ${recent_1h_vol:,.0f} < ${min_1h_vol:,.0f})")
            return None
        score     = rsi_score + ma_score + vol_score
        moon_maturity = calc_move_maturity(df_k, MATURITY_LOOKBACK)
        moon_mat_pen  = maturity_penalty(moon_maturity, max(score, 1.0),
                                          MATURITY_MOONSHOT_THRESHOLD)
        score = score - moon_mat_pen
        eff_moon_thresh = get_effective_threshold("MOONSHOT")
        # Apply regime multiplier only for entry scoring
        regime_mult = get_regime_multiplier()
        eff_moon_thresh_adj = eff_moon_thresh * regime_mult
        if score < eff_moon_thresh_adj:
            if moon_mat_pen > 0:
                log.debug(f"[MOONSHOT] Skip {sym} — maturity {moon_maturity:.2f} "
                          f"penalty -{moon_mat_pen:.1f}pts")
            return None
        keltner_bonus = 0.0
        if KELTNER_SCORE_BONUS > 0 and keltner_breakout(df_k):
            keltner_bonus = KELTNER_SCORE_BONUS
        if score > eff_moon_thresh_adj - 5:
            sentiment_delta, _ = sentiment_score_adjustment(sym)
            social_boost, social_summary = get_social_boost(sym)
        else:
            sentiment_delta, social_boost, social_summary = 0.0, 0.0, ""
        # In tightened regimes, reduce boosts so they can't push garbage over threshold
        if regime_mult > 1.05:
            boost_dampener = 1.0 / regime_mult  # e.g. 1.56× regime → boosts cut to 64%
            sentiment_delta = round(sentiment_delta * boost_dampener, 2)
            social_boost    = round(social_boost * boost_dampener, 2)
        final_score = round(score + keltner_bonus + sentiment_delta + social_boost, 2)

        # only apply social boost if already close to threshold
        if final_score < eff_moon_thresh_adj + 9:
            social_boost = 0.0
            social_summary = ""

        if final_score < eff_moon_thresh_adj:
            return None
        row_vol = ticker_vol_map.get(sym, 0.0)
        if check_dead_coin(sym, row_vol, 0.0, "MOONSHOT"):
            return None
        change_1h = ticker_change_map.get(sym, 0.0)
        vol_zscore = round(calc_vol_zscore(volume), 2)
        return {
            "symbol":       sym,
            "score":        final_score,
            "rsi":          round(rsi, 2),
            "rsi_delta":    round(rsi_delta, 2),
            "vol_ratio":    round(vol_ratio, 2),
            "vol_zscore":   vol_zscore,
            "vol_1h_usdt":  round(recent_1h_vol, 0),
            "entry_signal": classify_entry_signal(crossed_now=crossed,
                                                   vol_ratio=vol_ratio, rsi=rsi,
                                                   is_new=is_new,
                                                   is_trending=(sym in trending_syms),
                                                   label="MOONSHOT"),
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
                + (f" | z={best.get('vol_zscore',0):.1f}" if best.get('vol_zscore') else "")
                + (f" | 🔥 {best['_trend_reason']}" if best.get("_trend_reason") else ""))

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
        safe_opens  = opens.replace(0, np.nan)
        candle_moves= (close - opens).abs() / safe_opens * 100
        avg_move    = candle_moves.iloc[-11:-1].mean()
        price_burst = (float(candle_moves.iloc[-1]) / avg_move) if avg_move > 0 else 1.0
        greens      = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])
        vol_zscore   = s.get("vol_zscore", 0.0)
        vol_ratio_ok = s.get("vol_ratio", 1.0) >= VOL_RATIO_FLOOR
        zscore_ok    = vol_zscore >= VOL_ZSCORE_MIN and vol_ratio_ok
        if not zscore_ok and price_burst < 2.0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — burst not significant "
                     f"(z={vol_zscore:.1f} ratio={s.get('vol_ratio',0):.1f}× "
                     f"price_burst={price_burst:.1f}×)")
            continue
        if greens == 0:
            log.info(f"[MOONSHOT] Skip {s['symbol']} — both candles red")
            continue
        tradeable.append(s)

    if not tradeable:
        log.info("[MOONSHOT] No pairs passed burst check.")
        return None
    return pick_tradeable(tradeable, budget, "MOONSHOT")

def evaluate_reversal_candidate(sym: str) -> dict | None:
    df5m = parse_klines(sym, interval="5m", limit=60, min_len=30)
    if df5m is None:
        return None
    close  = df5m["close"]
    opens  = df5m["open"]
    volume = df5m["volume"]
    lows   = df5m["low"]
    rsi = calc_rsi(close)
    if np.isnan(rsi) or rsi > REVERSAL_MAX_RSI:
        return None

    avg_vol = float(volume.iloc[-22:-2].mean())
    if avg_vol <= 0:
        return None

    # Scan last 5 candles for capitulation (big red + high vol) followed by bounce (green)
    best_cap = None
    for offset in range(2, 6):
        if offset >= len(close):
            continue
        cap_open  = float(opens.iloc[-offset])
        cap_close = float(close.iloc[-offset])
        cap_low   = float(lows.iloc[-offset])
        cap_vol   = float(volume.iloc[-offset])
        # Must be red candle with elevated volume
        if cap_close >= cap_open:
            continue
        if cap_vol < avg_vol * 1.5:
            continue
        cap_body = cap_open - cap_close
        if cap_body <= 0:
            continue
        # Check if ANY subsequent candle is green (bounce confirmation)
        bounce_found = False
        best_recovery = 0.0
        best_bounce_vol = 0.0
        for bounce_idx in range(offset - 1, 0, -1):
            b_open  = float(opens.iloc[-bounce_idx])
            b_close = float(close.iloc[-bounce_idx])
            b_vol   = float(volume.iloc[-bounce_idx])
            if b_close > b_open:
                recovery = (b_close - b_open) / cap_body
                if recovery > best_recovery:
                    best_recovery = recovery
                    best_bounce_vol = b_vol
                    bounce_found = True
        if not bounce_found or best_recovery < REVERSAL_BOUNCE_RECOVERY:
            continue
        if best_bounce_vol < avg_vol * REVERSAL_VOL_RECOVERY:
            continue
        # This is a valid capitulation + bounce pattern
        if best_cap is None or cap_body > best_cap["cap_body"]:
            best_cap = {
                "cap_body": cap_body,
                "cap_low": cap_low,
                "recovery": best_recovery,
                "cap_vol": cap_vol,
                "bounce_vol": best_bounce_vol,
            }

    if best_cap is None:
        return None

    entry_est   = float(close.iloc[-1])
    cap_sl_pct  = max(
        REVERSAL_SL,
        (entry_est - best_cap["cap_low"]) / entry_est + REVERSAL_CAP_SL_BUFFER
    )
    cap_sl_pct  = min(cap_sl_pct, REVERSAL_SL_MAX)
    return {
        "symbol":      sym,
        "price":       entry_est,
        "rsi":         round(rsi, 2),
        "entry_signal":"CAPITULATION_BOUNCE",
        "score":       round((REVERSAL_MAX_RSI - rsi) + best_cap["recovery"] * 20
                             + (best_cap["bounce_vol"] / avg_vol), 2),
        "recovery":    round(best_cap["recovery"], 3),
        "cap_vol_ratio": round(best_cap["cap_vol"] / avg_vol, 2),
        "bounce_vol_ratio": round(best_cap["bounce_vol"] / avg_vol, 2),
        "cap_sl_pct":  round(cap_sl_pct, 4),
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
    tradeable.sort(key=lambda x: x["score"], reverse=True)
    best = tradeable[0]
    last_top_alt = best
    scanner_log(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | "
                f"Recovery: {best.get('recovery',0)*100:.0f}% | "
                f"BounceVol: {best.get('bounce_vol_ratio',0):.1f}× | "
                f"SL: -{best.get('cap_sl_pct',REVERSAL_SL)*100:.1f}%")
    return pick_tradeable(tradeable, budget, "REVERSAL")

def evaluate_prebreakout_candidate(sym: str) -> dict | None:
    df = parse_klines(sym, interval="5m", limit=60, min_len=30)
    if df is None:
        return None
    close  = df["close"]
    high   = df["high"]
    low    = df["low"]
    volume = df["volume"]
    opens  = df["open"]
    price_now = float(close.iloc[-1])
    if price_now <= 0:
        return None
    rsi = calc_rsi(close)
    if np.isnan(rsi) or rsi > 70 or rsi < 25:
        return None
    rsi_prev  = calc_rsi(close.iloc[:-1])
    rsi_delta = round(rsi - rsi_prev, 2) if not np.isnan(rsi_prev) else 0.0
    ema21 = calc_ema(close, 21)
    above_ema21 = price_now > float(ema21.iloc[-1])
    atr     = calc_atr(df, period=14)
    atr_pct = atr / price_now if price_now > 0 else 0.01
    pattern = None
    score   = 0.0
    n = PRE_BREAKOUT_ACCUM_CANDLES
    if len(volume) >= n + 2:
        recent_vol = volume.iloc[-(n + 1):]
        vol_vals   = [float(v) for v in recent_vol.values]
        vol_ups = sum(1 for i in range(len(vol_vals) - 1) if vol_vals[i + 1] > vol_vals[i])
        if vol_ups >= n - 1:
            recent_close = [float(c) for c in close.iloc[-(n + 1):].values]
            p_high, p_low = max(recent_close), min(recent_close)
            p_mid = (p_high + p_low) / 2 if (p_high + p_low) > 0 else 1.0
            p_range = (p_high - p_low) / p_mid
            if p_range < PRE_BREAKOUT_ACCUM_PRICE_RANGE:
                pattern = "ACCUMULATION"
                vol_growth = vol_vals[-1] / vol_vals[0] if vol_vals[0] > 0 else 1.0
                score = 30 + min(30, vol_growth * 10) + max(0, (1.0 - p_range / PRE_BREAKOUT_ACCUM_PRICE_RANGE) * 20)
    if pattern is None and above_ema21:
        lookback = min(PRE_BREAKOUT_SQUEEZE_LOOKBACK, len(df) - 5)
        if lookback >= 10:
            tr = pd.concat([
                high - low,
                (high - close.shift(1)).abs(),
                (low  - close.shift(1)).abs(),
            ], axis=1).max(axis=1)
            atr_series = tr.ewm(alpha=1.0 / 14, adjust=False).mean()
            recent_atrs = atr_series.iloc[-lookback:]
            current_atr = float(atr_series.iloc[-1])
            min_atr     = float(recent_atrs.min())
            if current_atr > 0 and current_atr <= min_atr * 1.10:
                pattern = "SQUEEZE"
                ema_dist = (price_now / float(ema21.iloc[-1]) - 1)
                score = 35 + min(20, ema_dist * 500) + min(25, (1.0 - current_atr / float(recent_atrs.mean())) * 50)
    if pattern is None:
        lookback = 30
        if len(df) >= lookback:
            recent = df.iloc[-lookback:]
            lows_window = recent["low"].values
            support_level = float(min(lows_window))
            tolerance     = support_level * 0.005
            touches = []
            for i, l in enumerate(lows_window):
                if abs(float(l) - support_level) <= tolerance:
                    touches.append(i)
            if len(touches) >= PRE_BREAKOUT_BASE_TESTS:
                red_vols_at_touches = []
                for idx in touches:
                    c = float(recent["close"].iloc[idx])
                    o = float(recent["open"].iloc[idx])
                    if c < o:
                        red_vols_at_touches.append(float(recent["volume"].iloc[idx]))
                if len(red_vols_at_touches) >= 2:
                    if red_vols_at_touches[-1] < red_vols_at_touches[0] * 0.8:
                        if price_now > support_level * 1.005:
                            pattern = "BASE_SPRING"
                            vol_decline = 1.0 - (red_vols_at_touches[-1] / red_vols_at_touches[0])
                            score = 30 + len(touches) * 5 + min(25, vol_decline * 40)
    if pattern is None:
        return None
    score = round(min(score, 100), 2)
    # Volume floor — reject dead coins where low vol mimics patterns
    avg_vol = float(volume.iloc[-20:-1].mean()) if len(volume) >= 21 else 0.0
    vol_ratio = round(float(volume.iloc[-1]) / avg_vol, 2) if avg_vol > 0 else 0.0
    if vol_ratio < 0.5:
        log.debug(f"[PRE_BREAKOUT] Skip {sym} — vol {vol_ratio:.1f}x too low for {pattern}")
        return None
    log.debug(f"🔮 [PRE_BREAKOUT] {sym} {pattern} | score={score:.0f} | "
              f"RSI={rsi:.0f} | ATR={atr_pct*100:.2f}% | Vol={vol_ratio:.1f}x")
    return {
        "symbol":       sym,
        "price":        price_now,
        "score":        score,
        "rsi":          round(rsi, 2),
        "rsi_delta":    rsi_delta,
        "atr_pct":      round(atr_pct, 6),
        "entry_signal": pattern,
        "vol_ratio":    vol_ratio,
    }

def find_prebreakout_opportunity(tickers: pd.DataFrame, budget: float,
                                  exclude: set, open_symbols: set) -> dict | None:
    df = tickers.copy()
    df = df[df["quoteVolume"] >= PRE_BREAKOUT_MIN_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    now_ts = time.time()
    df = df[~df["symbol"].apply(lambda s: _liquidity_blacklist.get(s, 0) > now_ts)]
    df = df[(df["priceChangePercent"].abs() >= 0.5) & (df["priceChangePercent"].abs() <= 10)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(30)["symbol"].tolist()
    log.info(f"🔮 [PRE_BREAKOUT] Scanning {len(candidates)} candidates")
    if not candidates:
        return None
    ticker_vol_map = dict(zip(df["symbol"], df["quoteVolume"].fillna(0)))
    scored = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(evaluate_prebreakout_candidate, sym): sym for sym in candidates}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result and result["score"] >= 30:
                    vol_24h = ticker_vol_map.get(result["symbol"], 0)
                    if not check_dead_coin(result["symbol"], vol_24h, 0.0, "MOONSHOT"):
                        scored.append(result)
            except Exception as e:
                log.debug(f"[PRE_BREAKOUT] Score failed for {futures[f]}: {e}")
    if not scored:
        scanner_log("🔮 [PRE_BREAKOUT] No qualifying patterns.")
        return None
    scored.sort(key=lambda x: x["score"], reverse=True)
    best = scored[0]
    scanner_log(f"🔮 [PRE_BREAKOUT] Top: {best['symbol']} | {best['entry_signal']} | "
                f"Score: {best['score']:.0f} | RSI: {best['rsi']}")
    return pick_tradeable(scored, budget, "PRE_BREAKOUT")

def evaluate_trinity_candidate(sym: str) -> dict | None:
    df = parse_klines(sym, interval=TRINITY_INTERVAL, limit=200, min_len=50)
    if df is None:
        return None
    close  = df["close"]
    volume = df["volume"]
    opens  = df["open"]
    price_now = float(close.iloc[-1])
    best_drop = 0.0
    for candles_back in TRINITY_DROP_LOOKBACK_CANDLES:
        if len(close) > candles_back + 1:
            price_then = float(close.iloc[-(candles_back + 1)])
            drop = (price_then - price_now) / price_then if price_then > 0 else 0.0
            best_drop = max(best_drop, drop)
    if best_drop < TRINITY_DROP_PCT:
        return None
    rsi = calc_rsi(close)
    if np.isnan(rsi) or not (TRINITY_MIN_RSI <= rsi <= TRINITY_MAX_RSI):
        return None
    # Bounce confirmation: at least 1 green candle (or doji with lower wick) in last 3
    greens = sum(1 for i in [-3, -2, -1]
                 if abs(i) <= len(close) and float(close.iloc[i]) >= float(opens.iloc[i]))
    if greens == 0:
        # Also accept a doji with a lower wick (buying pressure even if close ≈ open)
        last_body  = abs(float(close.iloc[-1]) - float(opens.iloc[-1]))
        last_range = float(df["high"].iloc[-1]) - float(df["low"].iloc[-1])
        has_buying_wick = last_range > 0 and last_body / last_range < 0.3
        if not has_buying_wick:
            return None
    avg_vol   = float(volume.iloc[-21:-1].mean())
    curr_vol  = float(volume.iloc[-1])
    vol_burst = (curr_vol / avg_vol) if avg_vol > 0 else 1.0
    if vol_burst < TRINITY_VOL_BURST:
        return None
    atr     = calc_atr(df, period=14)
    atr_pct = atr / price_now if price_now > 0 else 0.01
    tp_pct = max(TRINITY_TP_MIN, atr_pct * TRINITY_TP_ATR_MULT)
    sl_pct = min(TRINITY_SL_MAX, atr_pct * TRINITY_SL_ATR_MULT)
    if sl_pct > 0 and tp_pct / sl_pct < 1.5:
        tp_pct = sl_pct * 1.8
    log.info(f"⚡ [TRINITY] {sym} | drop {best_drop*100:.1f}% | RSI {rsi:.0f} | "
             f"vol {vol_burst:.1f}× | TP +{tp_pct*100:.2f}% SL -{sl_pct*100:.2f}% "
             f"R:R {tp_pct/sl_pct:.1f}:1")
    return {
        "symbol":       sym,
        "price":        price_now,
        "rsi":          round(rsi, 2),
        "vol_ratio":    round(vol_burst, 2),
        "entry_signal": "DEEP_DIP_RECOVERY",
        "atr_pct":      round(atr_pct, 6),
        "tp_pct":   round(tp_pct, 6),
        "sl_pct":   round(sl_pct, 6),
        "drop_pct": round(best_drop * 100, 2),
    }

def find_trinity_opportunity(balance: float,
                              exclude: set, open_symbols: set) -> dict | None:
    trinity_count = sum(1 for t in alt_trades if t.get("label") == "TRINITY")
    if trinity_count >= TRINITY_MAX_CONCURRENT:
        return None
    for sym in TRINITY_SYMBOLS:
        if sym in open_symbols or sym in exclude or sym in _api_blacklist:
            continue
        opp = evaluate_trinity_candidate(sym)
        if opp:
            scanner_log(f"⚡ TRINITY: {sym} down {opp['drop_pct']:.1f}% | "
                        f"RSI {opp['rsi']:.0f} | vol {opp['vol_ratio']:.1f}× | "
                        f"TP +{opp['tp_pct']*100:.2f}%")
            return opp
    return None

# ⚡ UPGRADE: Hybrid order placement (maker first, fallback to market)
def place_buy_order(symbol: str, qty: float, label: str, use_maker: bool = True) -> dict | None:
    """
    Place a buy order. If use_maker=True, attempt a post-only limit order at the best ask,
    wait up to MAKER_ORDER_TIMEOUT_SEC seconds, and if unfilled, cancel and place a market order.
    Returns order dict (with orderId) or None on failure.
    """
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] BUY {qty} {symbol}")
        return {"orderId": f"PAPER_BUY_{int(time.time())}"}

    # Fetch current price and depth for maker order
    if use_maker:
        try:
            depth = public_get("/api/v3/depth", {"symbol": symbol, "limit": 5})
            asks = depth.get("asks", [])
            if not asks:
                log.warning(f"[{label}] No asks in depth for {symbol} — falling back to market")
                use_maker = False
            else:
                best_ask = float(asks[0][0])
                # round to tick size
                _, _, _, tick_size = get_symbol_rules(symbol)
                price = round_price_to_tick(best_ask, tick_size)
        except Exception as e:
            log.warning(f"[{label}] Failed to get depth for maker order: {e} — falling back to market")
            use_maker = False
    else:
        price = None

    if use_maker:
        try:
            # Place post-only limit order
            order_params = {
                "symbol": symbol,
                "side": "BUY",
                "type": "LIMIT",
                "quantity": str(qty),
                "price": str(price),
                "postOnly": "true"   # ensures maker
            }
            result = private_post("/api/v3/order", order_params)
            order_id = result.get("orderId")
            log.info(f"✅ [{label}] Maker limit order placed: {order_id} @ {price}")

            # Wait for fill
            start = time.time()
            while time.time() - start < MAKER_ORDER_TIMEOUT_SEC:
                # Check order status
                status_resp = private_get("/api/v3/order", {"symbol": symbol, "orderId": order_id})
                if status_resp.get("status") == "FILLED":
                    # Order filled
                    log.info(f"✅ [{label}] Maker order filled: {order_id}")
                    # Fetch fills for accurate price
                    fills = get_actual_fills(symbol, since_ms=int(start * 1000), buy_order_id=order_id)
                    if fills.get("avg_buy_price"):
                        # update price in result (not used directly)
                        pass
                    return result
                elif status_resp.get("status") in ("CANCELED", "EXPIRED"):
                    break
                time.sleep(0.2)
            # If we reach here, order not filled in time
            log.info(f"⏰ [{label}] Maker order {order_id} not filled in {MAKER_ORDER_TIMEOUT_SEC}s — cancelling")
            cancel_order(symbol, order_id, label)
        except Exception as e:
            log.warning(f"[{label}] Maker order failed: {e} — falling back to market")

    # Fallback to market order
    try:
        result = private_post("/api/v3/order", {
            "symbol": symbol, "side": "BUY", "type": "MARKET", "quantity": str(qty)
        })
        log.info(f"✅ [{label}] Market BUY placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:    body = e.response.json()
        except Exception: body = e.response.text if e.response else "no response"
        if isinstance(body, dict) and body.get("code") == 10007:
            _api_blacklist.add(symbol)
            log.warning(f"⚠️ [{label}] {symbol} not API-tradeable — blacklisted.")
        else:
            log.error(f"🚨 [{label}] BUY rejected: {body}")
            telegram(f"🚨 <b>BUY rejected</b> {label} {symbol}\n{str(body)[:200]}")
        return None

# ⚡ UPGRADE: Maker orders for TP (post‑only if enabled)
def place_limit_sell(symbol, qty, price, label="", tag="", maker: bool = None):
    if maker is None:
        maker = USE_MAKER_ORDERS
    if PAPER_TRADE:
        return f"PAPER_{tag}_{int(time.time())}"
    try:
        order_params = {
            "symbol": symbol,
            "side": "SELL",
            "type": "LIMIT",
            "quantity": str(qty),
            "price": str(price)
        }
        if maker:
            order_params["postOnly"] = "true"
        result = private_post("/api/v3/order", order_params)
        order_id = result.get("orderId")
        maker_str = " (maker)" if maker else ""
        log.info(f"✅ [{label}] LIMIT SELL{maker_str} ({tag}): {order_id} @ {price}")
        return order_id
    except requests.exceptions.HTTPError as e:
        try:    body = e.response.json()
        except Exception: body = e.response.text if e.response else "no response"
        # Treat "order already filled/cancelled" (30005) as success (position already closed)
        if isinstance(body, dict) and body.get("code") == 30005:
            log.info(f"✅ [{label}] Order already closed (code 30005) for {symbol} — assuming closed")
            return None
        log.error(f"🚨 [{label}] LIMIT SELL rejected: {body}")
        telegram(f"⚠️ <b>TP limit failed</b> {label} {symbol} | bot monitoring instead")
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

def cancel_all_orders(symbol: str):
    """Cancel all open orders for a given symbol."""
    if PAPER_TRADE:
        return
    try:
        open_orders = private_get("/api/v3/openOrders", {"symbol": symbol})
        for order in open_orders:
            order_id = order["orderId"]
            try:
                private_delete("/api/v3/order", {"symbol": symbol, "orderId": order_id})
                log.info(f"✅ Cancelled order {order_id} for {symbol}")
            except Exception as e:
                log.debug(f"Failed to cancel order {order_id}: {e}")
    except Exception as e:
        log.debug(f"Failed to fetch open orders for {symbol}: {e}")

def get_order_details(symbol: str, order_id: int) -> dict:
    """Fetch order details from exchange. Returns dict with keys: status, executedQty, cummulativeQuoteQty, etc."""
    try:
        order = private_get("/api/v3/order", {"symbol": symbol, "orderId": order_id})
        return order
    except Exception as e:
        log.debug(f"Failed to get order details for {symbol} {order_id}: {e}")
        return {}

def get_actual_fills(symbol: str, since_ms: int, retries: int = 3,
                     buy_order_id=None, sell_order_ids: set | None = None) -> dict:
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
            if buy_order_id:
                buys = [f for f in all_buys if str(f.get("orderId")) == str(buy_order_id)]
                if not buys:
                    buys = all_buys
            else:
                buys = all_buys
            if sell_order_ids:
                sells = [f for f in all_sells if str(f.get("orderId")) in
                         {str(s) for s in sell_order_ids}]
                if not sells:
                    sells = all_sells
            else:
                sells = all_sells
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
                "qty":            qty_bought,
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

def calc_dynamic_tp_sl(opp: dict) -> tuple[float, float, str, str]:
    atr_pct        = opp.get("atr_pct",        0.015)
    vol_ratio      = opp.get("vol_ratio",       1.0)
    rsi            = opp.get("rsi",             50.0)
    score          = opp.get("score",           0.0)
    crossed_now    = opp.get("crossed_now",     False)
    ema21_dist_pct = opp.get("ema21_dist_pct",  atr_pct * 1.5)
    avg_candle_pct = opp.get("avg_candle_pct",  atr_pct)
    signal         = opp.get("entry_signal",
                             classify_entry_signal(crossed_now=crossed_now,
                                                    vol_ratio=vol_ratio, rsi=rsi))
    tp_mult  = _SIGNAL_TP_MULT.get(signal, SCALPER_TP_MULT_DEFAULT)
    tp_label = f"{signal.lower()}×{tp_mult}"
    atr_tp      = atr_pct * tp_mult
    candle_cap  = avg_candle_pct * SCALPER_TP_CANDLE_MULT
    tp_pct      = min(atr_tp, candle_cap)
    dynamic_tp_floor = calc_fee_aware_tp_floor()
    # Regime-adaptive TP cap: wider in bull (captures bigger moves), tighter stays default
    effective_tp_max = SCALPER_TP_MAX / min(_market_regime_mult, 1.0) if _market_regime_mult < 1.0 else SCALPER_TP_MAX
    tp_pct      = min(effective_tp_max, max(SCALPER_TP_MIN, dynamic_tp_floor, tp_pct))
    if atr_tp > candle_cap:
        tp_label += f" (candle-capped {candle_cap*100:.1f}%)"
    if signal in _SIGNAL_SL_MULT:
        sl_mult  = _SIGNAL_SL_MULT[signal]
        sl_label = f"tight×{sl_mult} ({signal.lower()})"
    elif score >= SCALPER_BREAKEVEN_SCORE:
        sl_mult  = SCALPER_SL_MULT_HIGH_CONF
        sl_label = f"wide×{sl_mult} (high confidence)"
    else:
        sl_mult  = SCALPER_SL_MULT_DEFAULT
        sl_label = f"standard×{sl_mult}"
    atr_sl      = atr_pct * sl_mult
    if signal == "CROSSOVER" and ema21_dist_pct > 0:
        sl_pct   = max(atr_sl, ema21_dist_pct)
        sl_label = f"EMA21 anchor ({ema21_dist_pct*100:.2f}%)"
    else:
        sl_pct   = atr_sl
    noise_floor = avg_candle_pct * SCALPER_SL_NOISE_MULT
    if sl_pct < noise_floor:
        sl_pct   = noise_floor
        sl_label += f" (noise-floored {noise_floor*100:.2f}%)"
    sl_pct = min(SCALPER_SL_MAX, max(SCALPER_SL_MIN, sl_pct))
    log.info(f"[SCALPER] Dynamic TP: {tp_pct*100:.2f}% [{tp_label}] | "
             f"SL: {sl_pct*100:.2f}% [{sl_label}] | "
             f"R:R {tp_pct/sl_pct:.1f}:1")
    return tp_pct, sl_pct, tp_label, sl_label

def calc_risk_budget(opp: dict, balance: float) -> tuple[float, float, float, str, str]:
    score = opp.get("score", SCALPER_THRESHOLD)
    gap   = score - SCALPER_THRESHOLD
    if   gap < 15: kelly_mult = KELLY_MULT_MARGINAL
    elif gap < 30: kelly_mult = KELLY_MULT_SOLID
    elif gap < 45: kelly_mult = KELLY_MULT_STANDARD
    else:          kelly_mult = KELLY_MULT_HIGH_CONF

    tp_pct, sl_pct, tp_label, sl_label = calc_dynamic_tp_sl(opp)
    if sl_pct > 0:
        risk_per_trade = min(SCALPER_RISK_PER_TRADE * kelly_mult, 0.028)
        risk_budget = balance * risk_per_trade / sl_pct
        eff_budget_pct = get_effective_budget_pct("SCALPER")
        capped = min(risk_budget, balance * eff_budget_pct)
        log.debug(f"[SCALPER] Kelly mult {kelly_mult:.2f}×, risk {risk_per_trade*100:.2f}% → ${capped:.2f}")
        return round(capped, 2), tp_pct, sl_pct, tp_label, sl_label
    return round(balance * get_effective_budget_pct("SCALPER"), 2), 0.0, 0.0, "", ""

# ⚡ NEW: Chase limit order for profit exits (reduces slippage)
def chase_limit_sell(symbol: str, qty: float, label: str, tag: str = "", timeout: float = CHASE_LIMIT_TIMEOUT, max_retries: int = CHASE_LIMIT_RETRIES) -> dict | None:
    """
    Attempt to sell at the best ask using limit orders. Retries if not filled.
    Returns order result dict (with orderId) or None on failure.
    """
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] [{label}] CHASE LIMIT SELL ({tag}) {qty} {symbol}")
        return {"orderId": f"PAPER_{tag}_{int(time.time())}"}

    # Round qty to step_size upfront
    min_qty, step_size, _, _ = get_symbol_rules(symbol)
    d_qty  = Decimal(str(qty))
    d_step = Decimal(str(step_size))
    qty    = float((d_qty / d_step).to_integral_value(rounding=ROUND_DOWN) * d_step)
    if qty < min_qty:
        log.warning(f"[{label}] Chase sell qty {qty} < min {min_qty} for {symbol} — skipping")
        return None

    for attempt in range(max_retries):
        # Get current best ask
        try:
            depth = public_get("/api/v3/depth", {"symbol": symbol, "limit": 5})
            asks = depth.get("asks", [])
            if not asks:
                log.warning(f"[{label}] No asks in depth for {symbol} — falling back to market")
                break
            best_ask = float(asks[0][0])
            _, _, _, tick_size = get_symbol_rules(symbol)
            price = round_price_to_tick(best_ask, tick_size)
        except Exception as e:
            log.warning(f"[{label}] Failed to get ask price for {symbol}: {e} — falling back to market")
            break

        # Place limit order (not post-only)
        try:
            order_params = {
                "symbol": symbol,
                "side": "SELL",
                "type": "LIMIT",
                "quantity": str(qty),
                "price": str(price)
            }
            result = private_post("/api/v3/order", order_params)
            order_id = result.get("orderId")
            log.info(f"✅ [{label}] Chase limit order placed: {order_id} @ {price} (attempt {attempt+1})")

            # Wait for fill
            start = time.time()
            while time.time() - start < timeout:
                status_resp = private_get("/api/v3/order", {"symbol": symbol, "orderId": order_id})
                if status_resp.get("status") == "FILLED":
                    log.info(f"✅ [{label}] Chase limit order filled: {order_id}")
                    return result
                elif status_resp.get("status") in ("CANCELED", "EXPIRED"):
                    break
                time.sleep(0.2)

            # Not filled in time – cancel
            log.info(f"⏰ [{label}] Chase limit order {order_id} not filled in {timeout}s — cancelling and retrying")
            cancel_order(symbol, order_id, label)
        except requests.exceptions.HTTPError as e:
            try:    body = e.response.json()
            except Exception: body = e.response.text if e.response else "no response"
            err_code = body.get("code") if isinstance(body, dict) else None
            if err_code == 30005:
                log.info(f"✅ [{label}] Order already closed (code 30005) for {symbol} — assuming closed")
                return None
            if err_code == 400 or (isinstance(body, dict) and "scale" in str(body.get("msg", "")).lower()):
                # Qty precision error — re-fetch actual balance
                log.warning(f"⚠️ [{label}] Qty precision error (qty={qty}): {body} — re-fetching balance")
                qty = get_sellable_qty(symbol)
                if qty <= 0:
                    log.info(f"✅ [{label}] No sellable qty after re-fetch — position already closed")
                    return None
            else:
                log.warning(f"[{label}] Chase limit order failed on attempt {attempt+1}: {e}")
        except Exception as e:
            log.warning(f"[{label}] Chase limit order failed on attempt {attempt+1}: {e}")

        # Wait a moment before retry with progressive delay
        if attempt < max_retries - 1:
            time.sleep(0.5 * (attempt + 1))  # progressive: 0.5s, 1s, 1.5s

    # Fallback to market sell — re-fetch fresh balance and round
    sell_qty = get_sellable_qty(symbol, fallback_qty=qty)
    if sell_qty <= 0:
        log.info(f"✅ [{label}] No sellable qty for market fallback — position already closed")
        return None
    log.info(f"[{label}] Falling back to market sell for {symbol} qty={sell_qty}")
    try:
        result = private_post("/api/v3/order", {
            "symbol": symbol, "side": "SELL", "type": "MARKET", "quantity": str(sell_qty)
        })
        log.info(f"✅ [{label}] Market SELL placed: {result}")
        return result
    except requests.exceptions.HTTPError as e:
        try:    body = e.response.json()
        except Exception: body = e.response.text if e.response else "no response"
        if isinstance(body, dict) and body.get("code") == 30005:
            log.info(f"✅ [{label}] Order already closed (code 30005) for {symbol} — assuming closed")
            return None
        log.error(f"🚨 [{label}] Market SELL failed: {body}")
        telegram(f"🚨 <b>SELL failed!</b> {label} {symbol} | qty={sell_qty}\n{str(body)[:150]}")
        return None

def open_position(opp, budget_usdt, tp_pct, sl_pct, label, max_hours=None):
    symbol                              = opp["symbol"]
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
    bought_at_ms = int(time.time() * 1000)
    spread_limit = SCALPER_MAX_SPREAD if label in ("SCALPER", "TRINITY") else MOONSHOT_MAX_SPREAD
    if label in ("SCALPER", "MOONSHOT", "TRINITY") and not PAPER_TRADE:
        try:
            depth    = public_get("/api/v3/depth", {"symbol": symbol, "limit": DEPTH_BID_LEVELS})
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
                if DEPTH_BID_RATIO > 0:
                    depth_floor = best_bid * (1 - DEPTH_PCT_RANGE)
                    bid_usdt    = sum(
                        float(p) * float(q)
                        for p, q in bids
                        if float(p) >= depth_floor
                    )
                    min_depth = notional * DEPTH_BID_RATIO
                    if bid_usdt < min_depth:
                        log.info(f"[{label}] Skip {symbol} — thin book "
                                 f"(${bid_usdt:,.0f} bids within {DEPTH_PCT_RANGE*100:.0f}% "
                                 f"< ${min_depth:,.0f} required = {DEPTH_BID_RATIO:.0f}× "
                                 f"${notional:.2f} position)")
                        return None
                strategy_key = "SCALPER" if label in ("SCALPER", "TRINITY") else "MOONSHOT"
                check_dead_coin(symbol, 0.0, spread, strategy_key)
        except Exception:
            pass

    # ⚡ UPGRADE: Use maker orders for entries (configurable)
    use_maker = USE_MAKER_ORDERS and label not in ("REVERSAL",)  # reversal entries may need speed
    buy_order = place_buy_order(symbol, qty, label, use_maker=use_maker)
    if not buy_order:
        return None
    buy_order_id = buy_order.get("orderId")
    actual_fills = get_actual_fills(symbol, since_ms=bought_at_ms,
                                    buy_order_id=buy_order_id)
    actual_entry = actual_fills.get("avg_buy_price") or price
    actual_qty   = actual_fills.get("qty", qty) 
    actual_cost  = actual_fills.get("cost_usdt")     or notional
    if actual_fills.get("avg_buy_price"):
        log.info(f"[{label}] Actual fill: ${actual_entry:.6f} "
                 f"(ticker was ${price:.6f}, slippage: {(actual_entry/price-1)*100:+.3f}%)")
    else:
        log.info(f"[{label}] Using ticker price (myTrades unavailable): ${price:.6f}")

    # Now compute TP/SL prices first (needed for partial TP)
    # For SCALPER and REVERSAL, we may have dynamic SL, for others static
    if label == "SCALPER" and opp.get("atr_pct") is not None:
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
        actual_sl   = opp["cap_sl_pct"]
        tp_label    = ""
        sl_label    = f"cap-candle anchor (-{actual_sl*100:.1f}%)"
        tp_price    = round_price_to_tick(actual_entry * (1 + tp_pct), tick_size)
    else:
        used_tp_pct = tp_pct
        actual_sl   = sl_pct
        tp_label    = ""
        sl_label    = ""
        tp_price    = round_price_to_tick(actual_entry * (1 + tp_pct), tick_size)

    # 🔧 UPGRADE: ATR-based moonshot stop-loss
    if label == "MOONSHOT":
        atr_pct = opp.get("atr_pct", 0.02)
        # compute dynamic SL using ATR, capped between 4% and 12%
        dynamic_sl = max(0.04, min(0.12, atr_pct * MOONSHOT_SL_ATR_MULT))
        actual_sl = dynamic_sl
        sl_label = f"ATR×{MOONSHOT_SL_ATR_MULT} ({dynamic_sl*100:.1f}%)"
        sl_price = round(actual_entry * (1 - actual_sl), 8)
    else:
        sl_price = round(actual_entry * (1 - actual_sl), 8)

    # 🔧 NEW: Disable micro/partial TP for small trades to avoid dust
    micro_tp_price = None
    partial_tp_price = None
    if label == "MOONSHOT" and actual_cost < MIN_TRADE_FOR_PARTIAL_TP:
        log.info(f"[{label}] Trade size ${actual_cost:.2f} < ${MIN_TRADE_FOR_PARTIAL_TP:.0f} — disabling micro/partial TP")
        # micro and partial TP will remain None
    else:
        # compute micro and partial TP as usual
        if label == "MOONSHOT":
            micro_tp_price = round_price_to_tick(actual_entry * (1 + MOONSHOT_MICRO_TP_PCT), tick_size)
            partial_tp_price = round_price_to_tick(actual_entry * (1 + MOONSHOT_PARTIAL_TP_PCT), tick_size)
        elif label == "REVERSAL":
            partial_tp_price = round_price_to_tick(actual_entry * (1 + REVERSAL_PARTIAL_TP_PCT), tick_size)
        elif label == "SCALPER" and opp.get("score", 0) >= SCALPER_PARTIAL_TP_SCORE:
            partial_tp_price = tp_price   # now tp_price is defined

    # Place TP order with maker option (if enabled)
    if label in ("SCALPER", "TRINITY"):
        tp_order_id = place_limit_sell(symbol, actual_qty, tp_price, label, tag="TP", maker=USE_MAKER_ORDERS)
        if not PAPER_TRADE and not tp_order_id:
            log.warning(f"[{label}] TP limit failed — monitoring manually.")
            telegram(f"⚠️ {label} {symbol} TP limit failed — bot monitoring")
        tp_status = "TP ✅ on exchange" if tp_order_id else "TP monitored by bot"
    else:
        tp_order_id = None
        used_tp_pct = tp_pct
        tp_status   = "TP + SL bot-monitored ✅ (direct market sell)"

    # ── Floor & Chase fields added ─────────────────────────────────
    trade = {
        "label":          label,
        "symbol":         symbol,
        "entry_price":    actual_entry,
        "entry_ticker":   price,
        "qty":            actual_qty,
        "budget_used":    actual_cost,
        "bought_at_ms":   bought_at_ms,
        "buy_order_id":   buy_order_id,
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
        "entry_signal":   opp.get("entry_signal", "UNKNOWN"),
        "sentiment":      opp.get("sentiment"),
        "trail_pct":      opp.get("trail_pct", SCALPER_TRAIL_PCT) if label == "SCALPER" else None,
        "atr_pct":        opp.get("atr_pct") if opp.get("atr_pct") is not None else (
                              opp.get("trail_pct", SCALPER_TRAIL_PCT) if label == "SCALPER"
                              else actual_sl * 0.5
                          ),
        "vol_ratio":      opp.get("vol_ratio", 1.0),   # for micro‑cap detection
        "move_maturity":  opp.get("move_maturity"),
        "breakeven_act":  (SCALPER_BREAKEVEN_ACT if (
                               label == "SCALPER" and
                               opp.get("score", 0) >= SCALPER_BREAKEVEN_SCORE
                           ) else 0.025 if label == "SCALPER"  # wider 2.5% activation for lower-confidence scalpers
                           else MOONSHOT_BREAKEVEN_ACT if label == "MOONSHOT"
                           else TRINITY_BREAKEVEN_ACT if label == "TRINITY"
                           else None),
        "breakeven_done": False,
        "micro_tp_price": micro_tp_price,
        "micro_tp_ratio": MOONSHOT_MICRO_TP_RATIO if label == "MOONSHOT" else None,
        "micro_tp_hit":   False,
        "partial_tp_price": partial_tp_price,
        "partial_tp_ratio": (
            SCALPER_PARTIAL_TP_RATIO  if (label == "SCALPER" and opp.get("score", 0) >= SCALPER_PARTIAL_TP_SCORE) else
            MOONSHOT_PARTIAL_TP_RATIO if label == "MOONSHOT" else
            REVERSAL_PARTIAL_TP_RATIO if label == "REVERSAL" else None
        ),
        "partial_tp_hit":   False,
        # ── Floor & Chase fields ─────────────────────────────────────
        "hard_floor_price": None,
        "trailing_stop_price": None,
        "trailing_active": False,
        "last_tp_price": None,          # records the price at which a partial TP was taken
    }

    mode         = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    icon         = {"SCALPER":"🟢","MOONSHOT":"🌙","REVERSAL":"🔄","TRINITY":"🔱","PRE_BREAKOUT":"🔮"}.get(label,"🟢")
    slippage_line = ""
    if actual_fills.get("avg_buy_price") and abs(actual_entry - price) > 0.000001:
        slippage_pct  = (actual_entry / price - 1) * 100
        slippage_line = f"  slip {slippage_pct:+.3f}%"
    # Compact TP/SL line
    tp_sl_line = (f"TP <b>${tp_price:.6f}</b> (+{used_tp_pct*100:.1f}%) | "
                  f"SL ${sl_price:.6f} (-{actual_sl*100:.1f}%)")
    # Compact partial TP info
    exit_plan = ""
    if trade.get("micro_tp_price") and label == "MOONSHOT":
        micro_pct = (trade["micro_tp_price"] / actual_entry - 1) * 100
        exit_plan += f"μTP +{micro_pct:.1f}% → "
    if trade.get("partial_tp_price"):
        partial_pct = (trade["partial_tp_price"] / actual_entry - 1) * 100
        exit_plan += f"½TP +{partial_pct:.1f}% → "
    if label in ("MOONSHOT", "REVERSAL", "PRE_BREAKOUT"):
        exit_plan += "Floor & Chase"
    elif label == "SCALPER":
        exit_plan += "trail"
    exit_line = f"Exit: {exit_plan}\n" if exit_plan else ""
    # Score line
    score_parts = [f"Score {opp.get('score',0):.0f}",
                   f"{opp.get('entry_signal','?')}",
                   f"RSI {opp.get('rsi','?')}({opp.get('rsi_delta',0):+.1f})",
                   f"Vol {opp.get('vol_ratio','?')}x"]
    if opp.get("kelly_mult") and label == "SCALPER":
        score_parts.append(f"Kelly {opp['kelly_mult']:.1f}×")
    score_line = " | ".join(score_parts)
    # Build timeout/breakeven line
    timing_parts = []
    if max_hours:
        timing_parts.append(f"⏰ {max_hours}h")
    if trade.get("breakeven_act"):
        timing_parts.append(f"🔒 BE +{trade['breakeven_act']*100:.1f}%")
    timing_line = "  ".join(timing_parts)
    log.info(f"{icon} [{label}] Opened {symbol} | ${actual_cost:.2f} | "
             f"Entry: {actual_entry:.6f} | TP: {tp_price:.6f} (+{used_tp_pct*100:.1f}%) | "
             f"SL: {sl_price:.6f} (-{actual_sl*100:.1f}%)")
    telegram(
        f"{icon} <b>{label} — {symbol}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"${actual_cost:.2f} → <b>${actual_entry:.6f}</b>{slippage_line}\n"
        f"{tp_sl_line}\n"
        f"{exit_line}"
        f"{timing_line}\n"
        f"{score_line}"
    )
    save_state()
    return trade

# ── Floor & Chase activation (after partial TP) ──────────────────
def activate_floor_and_chase(trade, exit_price):
    """Setup floor & chase for the remaining position after a partial TP."""
    true_be = calculate_true_breakeven(trade["entry_price"])
    # Profit lock floor: max(true breakeven, exit_price * 0.995)
    hard_floor = max(true_be, exit_price * 0.995)
    trade["hard_floor_price"] = hard_floor
    trade["trailing_active"] = True
    trade["last_tp_price"] = exit_price

    # Compute initial trailing stop using progressive trail
    atr_pct = trade.get("atr_pct", 0.02)
    hwm = trade["highest_price"]
    peak_profit = (hwm / trade["entry_price"] - 1)
    label = trade.get("label", "MOONSHOT")
    trail_pct = calc_progressive_trail(peak_profit, atr_pct, strategy=label)
    trail_stop = hwm * (1 - trail_pct)
    # Ensure trail stop is not below hard floor
    trade["trailing_stop_price"] = max(trail_stop, hard_floor)
    log.info(f"🛡️ Floor & Chase activated: floor=${hard_floor:.6f}, "
             f"trail=${trade['trailing_stop_price']:.6f} "
             f"(prog {trail_pct*100:.1f}% at +{peak_profit*100:.1f}% profit)")

def check_exit(trade, best_score: float = 0) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")
    try:
        opened = datetime.fromisoformat(trade["opened_at"])
        if opened.tzinfo is None:
            opened = opened.replace(tzinfo=timezone.utc)
        held_min = (datetime.now(timezone.utc) - opened).total_seconds() / 60
    except Exception:
        held_min = 0.0
    if trade.get("max_hours"):
        if label == "MOONSHOT":
            if (not trade.get("partial_tp_hit") and not trade.get("micro_tp_hit")
                    and held_min >= MOONSHOT_TIMEOUT_MAX_MINS):
                log.info(f"⏰ [{label}] Max timeout ({MOONSHOT_TIMEOUT_MAX_MINS}min): {symbol}")
                return True, "TIMEOUT"
        else:
            if held_min / 60 >= trade["max_hours"]:
                log.info(f"⏰ [{label}] Timeout: {symbol}")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TIMEOUT"
    price = ws_price(symbol)
    if price is None:
        try:
            price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
        except Exception as e:
            log.error(f"Price fetch error {symbol}: {e}")
            return False, ""
    pct = (price - trade["entry_price"]) / trade["entry_price"] * 100
    peak_pct = (trade["highest_price"] / trade["entry_price"] - 1) * 100
    trade["highest_price"] = max(trade.get("highest_price", price), price)
    hard_sl_pct = -(trade.get("sl_pct", 0.05) * 100 + 4.0)
    if pct <= hard_sl_pct:
        log.info(f"🚨 [{label}] Hard SL: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"
    if price <= trade["sl_price"]:
        log.info(f"🛑 [{label}] SL: {symbol} | {pct:.2f}%")
        if not PAPER_TRADE and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
        return True, "STOP_LOSS"

    # ── MOONSHOT HIGH-WATER MARK WITH MICRO‑CAP AND ATR GIVEBACK ──
    if label == "MOONSHOT" and not trade.get("partial_tp_hit") and not trade.get("micro_tp_hit"):
        # Micro‑cap detection
        vol_ratio = trade.get("vol_ratio", 1.0)
        if vol_ratio < MICRO_CAP_VOL_RATIO_THRESHOLD:
            protect_act = MICRO_CAP_PROTECT_ACT       # 2.5%
            giveback = MICRO_CAP_GIVEBACK             # 0.5%
            reason_tag = "MICRO_HWM"
        else:
            protect_act = MOONSHOT_PROTECT_ACT        # 4.0%
            # Dynamic ATR-based giveback (floor = MOONSHOT_PROTECT_GIVEBACK)
            atr_pct = trade.get("atr_pct", 0.02)
            dynamic_giveback = max(MOONSHOT_PROTECT_GIVEBACK,
                                   min(0.03, atr_pct * MOONSHOT_HWM_ATR_MULT))
            giveback = dynamic_giveback
            reason_tag = "DYN_HWM"

        if peak_pct >= protect_act * 100:
            drop_from_peak = (trade["highest_price"] - price) / trade["highest_price"]
            if drop_from_peak >= giveback:
                log.info(f"🛡️ [{label}] {reason_tag} stop: {symbol} | peak +{peak_pct:.1f}%, drop {drop_from_peak*100:.1f}% → sell")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, reason_tag

    breakeven_act = trade.get("breakeven_act")
    if breakeven_act and not trade.get("breakeven_done") and peak_pct >= breakeven_act * 100:
        if trade["sl_price"] < trade["entry_price"]:
            trade["sl_price"]       = trade["entry_price"]
            trade["breakeven_done"] = True
            log.info(f"🔒 [{label}] Breakeven locked: {symbol} | peak +{peak_pct:.1f}% | "
                     f"SL moved to entry ${trade['entry_price']:.6f}")

    # Micro TP (if enabled) — dynamic ratio to guarantee minimum profit
    if (label == "MOONSHOT"
            and not trade.get("micro_tp_hit")
            and trade.get("micro_tp_price")
            and peak_pct >= MOONSHOT_MICRO_TP_PCT * 100):
        gain_per_unit = price - trade["entry_price"]
        total_qty     = trade["qty"]
        default_ratio = trade.get("micro_tp_ratio", MOONSHOT_MICRO_TP_RATIO)
        max_micro_ratio = 0.70  # never sell more than 70% as a "micro" TP

        if gain_per_unit > 0 and total_qty > 0:
            # Calculate minimum ratio needed to hit $1 profit (with small buffer for float precision)
            needed_ratio = (MICRO_TP_MIN_PROFIT * 1.01) / (total_qty * gain_per_unit)
            # Use the larger of default ratio or needed ratio, capped at 70%
            actual_ratio = max(default_ratio, min(needed_ratio, max_micro_ratio))
            estimated_profit = total_qty * actual_ratio * gain_per_unit

            if estimated_profit >= MICRO_TP_MIN_PROFIT:
                # Store dynamic ratio so execute_partial_tp uses it
                trade["micro_tp_ratio"] = round(actual_ratio, 3)
                log.info(f"🎯μ [{label}] Micro TP triggered: {symbol} | +{peak_pct:.1f}% | "
                         f"ratio {actual_ratio*100:.0f}% ({'default' if actual_ratio <= default_ratio else 'raised'}) | "
                         f"est ${estimated_profit:.2f}")
                return True, "MICRO_TP"

        # Position too small even at max ratio — raise SL to lock half the gain instead
        half_gain_price = trade["entry_price"] * (1 + (pct / 100) * 0.5)
        if half_gain_price > trade["sl_price"] * 1.002:
            old_sl = trade["sl_price"]
            trade["sl_price"] = round(half_gain_price, 8)
            log.info(f"[{label}] Micro TP too small for ${MICRO_TP_MIN_PROFIT:.0f} profit "
                     f"— SL raised ${old_sl:.6f} → ${half_gain_price:.6f} (+{pct/2:.1f}%)")

    # Partial TP (if enabled)
    if (label in ("MOONSHOT", "REVERSAL")
            and not trade.get("partial_tp_hit")
            and trade.get("partial_tp_price")
            and peak_pct >= (trade["partial_tp_price"] / trade["entry_price"] - 1) * 100):
        log.info(f"🎯½ [{label}] Partial TP triggered (peak): {symbol} | peak +{peak_pct:.1f}%")
        return True, "PARTIAL_TP"

    if label == "SCALPER":
        # --- New: Major partial fill detection ---
        if not PAPER_TRADE and tp_order_id and tp_order_id in get_open_order_ids(symbol):
            order = get_order_details(symbol, tp_order_id)
            if order and order.get("status") == "PARTIALLY_FILLED":
                filled_qty = float(order.get("executedQty", 0))
                if filled_qty > 0:
                    filled_ratio = filled_qty / trade["qty"]
                    remaining_qty = trade["qty"] - filled_qty
                    remaining_notional = remaining_qty * price
                    if filled_ratio >= MAJOR_FILL_THRESHOLD and remaining_notional < DUST_THRESHOLD:
                        log.info(f"🎯 [SCALPER] Major partial fill ({filled_ratio*100:.1f}%) for {symbol}, remaining dust (${remaining_notional:.2f}) – closing trade")
                        # Cancel remaining order
                        cancel_order(symbol, tp_order_id, label)
                        trade["tp_order_id"] = None
                        # Record the partial fill as a trade
                        filled_cost = float(order.get("cummulativeQuoteQty", 0))
                        filled_price = filled_cost / filled_qty if filled_qty > 0 else price
                        # P&L based on entry price (not budget_used which drifts)
                        actual_cost = round(trade["entry_price"] * filled_qty, 4)
                        actual_rev  = round(filled_qty * filled_price, 4)
                        actual_pnl  = round(actual_rev - actual_cost, 4)
                        actual_pct  = round((filled_price / trade["entry_price"] - 1) * 100, 4) if trade["entry_price"] > 0 else 0
                        partial_trade = trade.copy()
                        partial_trade["qty"] = filled_qty
                        partial_trade["budget_used"] = actual_cost
                        partial_trade["exit_price"] = filled_price
                        partial_trade["exit_ticker"] = filled_price
                        partial_trade["exit_reason"] = "MAJOR_PARTIAL_TP"
                        partial_trade["closed_at"] = datetime.now(timezone.utc).isoformat()
                        partial_trade["fee_usdt"] = 0
                        partial_trade["cost_usdt"] = actual_cost
                        partial_trade["revenue_usdt"] = actual_rev
                        partial_trade["pnl_usdt"] = actual_pnl
                        partial_trade["pnl_pct"] = actual_pct
                        partial_trade["fills_used"] = True
                        partial_trade["is_partial"] = True
                        trade_history.append(partial_trade)
                        # Sync remaining with exchange (properly rounded)
                        synced_remaining = get_sellable_qty(symbol)
                        trade["qty"] = synced_remaining if synced_remaining >= 0 else remaining_qty
                        trade["budget_used"] = round(trade["entry_price"] * trade["qty"], 4)
                        return True, "MAJOR_PARTIAL_TP"
        # --- End major partial fill detection ---

        if (trade.get("partial_tp_price")
                and not trade.get("partial_tp_hit")
                and peak_pct >= (trade["partial_tp_price"] / trade["entry_price"] - 1) * 100):
            if PAPER_TRADE or not tp_order_id or tp_order_id not in get_open_order_ids(symbol):
                log.info(f"🎯½ [SCALPER] Partial TP triggered (peak): {symbol} | peak +{peak_pct:.1f}%")
                return True, "PARTIAL_TP"
        if not PAPER_TRADE and tp_order_id:
            near_tp = price >= trade["tp_price"] * 0.98
            if near_tp and tp_order_id not in get_open_order_ids(symbol):
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
        atr_pct   = trade.get("atr_pct") or trade.get("trail_pct") or SCALPER_TRAIL_PCT
        peak_profit = (trade["highest_price"] / trade["entry_price"] - 1)

        # Progressive trail: activate once profit exceeds activation threshold
        trail_activated = (peak_profit >= atr_pct * SCALPER_TRAIL_ATR_ACTIVATE
                           or trade.get("partial_tp_hit"))
        if trail_activated:
            active_trail = calc_progressive_trail(peak_profit, atr_pct, strategy="SCALPER")
            trail_label  = f"prog {active_trail*100:.1f}%"
            if price <= trade["highest_price"] * (1 - active_trail):
                log.info(f"📉 [{label}] Progressive trail ({trail_label}): {symbol} | {pct:+.2f}% "
                         f"| peak +{peak_profit*100:.1f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TRAILING_STOP"
        else:
            trail_pct = trade.get("trail_pct") or SCALPER_TRAIL_PCT
            if trade["highest_price"] >= trade["entry_price"] * (1 + SCALPER_TRAIL_ACT):
                if price <= trade["highest_price"] * (1 - trail_pct):
                    log.info(f"📉 [{label}] Trailing stop (legacy {trail_pct*100:.1f}%): "
                             f"{symbol} | {pct:+.2f}%")
                    if not PAPER_TRADE and tp_order_id:
                        cancel_order(symbol, tp_order_id, label)
                    return True, "TRAILING_STOP"
        if held_min >= SCALPER_FLAT_MINS and abs(pct) <= SCALPER_FLAT_RANGE * 100:
            log.info(f"😴 [{label}] Flat exit: {symbol} | {pct:+.2f}%")
            if not PAPER_TRADE and tp_order_id:
                cancel_order(symbol, tp_order_id, label)
            return True, "FLAT_EXIT"
        if best_score > 0 and pct < SCALPER_TRAIL_ACT * 100:
            rotate_gap = SCALPER_ROTATE_GAP * (0.7 if best_score <= 70 else 1.0)
            if best_score - trade.get("score", 0) >= rotate_gap:
                log.info(f"🔀 [{label}] Rotation: {symbol} | {pct:+.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "ROTATION"

    # ── FLOOR & CHASE EXIT (for MOONSHOT, REVERSAL, PRE_BREAKOUT) ──
    elif label in ("MOONSHOT", "REVERSAL", "PRE_BREAKOUT") and trade.get("trailing_active"):
        # Update HWM and trailing stop if price rises
        if price > trade.get("highest_price", trade["entry_price"]):
            trade["highest_price"] = price
            atr_pct = trade.get("atr_pct", 0.02)
            peak_profit = (trade["highest_price"] / trade["entry_price"] - 1)
            # Progressive trail: tightens as profit grows, adjusts for volatility
            trail_pct = calc_progressive_trail(peak_profit, atr_pct, strategy=label)
            new_trail = trade["highest_price"] * (1 - trail_pct)
            # Trail can only go up
            if new_trail > trade.get("trailing_stop_price", 0):
                trade["trailing_stop_price"] = new_trail
                log.debug(f"Progressive trail updated: ${new_trail:.6f} "
                          f"(trail {trail_pct*100:.1f}% at +{peak_profit*100:.1f}% profit) "
                          f"for {symbol}")

        hard_floor = trade.get("hard_floor_price")
        trail_stop = trade.get("trailing_stop_price")
        if hard_floor is not None and trail_stop is not None:
            active_trigger = max(trail_stop, hard_floor)
            triggered_by = "floor" if hard_floor >= trail_stop else "trail"
            if price <= active_trigger:
                curr_peak = (trade["highest_price"] / trade["entry_price"] - 1)
                curr_trail_pct = calc_progressive_trail(
                    curr_peak, trade.get("atr_pct", 0.02), strategy=label)
                log.info(f"🛡️ Floor & Chase exit: {symbol} | price {price:.6f} ≤ "
                         f"{triggered_by} {active_trigger:.6f} | "
                         f"trail {curr_trail_pct*100:.1f}% at peak +{curr_peak*100:.1f}% | "
                         f"P&L {pct:.2f}%")
                if not PAPER_TRADE and trade.get("tp_order_id"):
                    cancel_order(symbol, trade["tp_order_id"], label)
                    trade["tp_order_id"] = None
                return True, "FLOOR_OR_TRAIL"

    # ── FALLBACK TRAILING FOR MOONSHOT (if no floor & chase active) ──
    elif label == "MOONSHOT" and trade.get("partial_tp_hit") and not trade.get("trailing_active"):
        atr_pct     = trade.get("atr_pct") or MOONSHOT_SL * 0.5
        peak_profit = (trade["highest_price"] / trade["entry_price"] - 1)
        trail_pct   = calc_progressive_trail(peak_profit, atr_pct, strategy="MOONSHOT")
        trail_sl    = trade["highest_price"] * (1 - trail_pct)
        if price <= trail_sl:
            log.info(f"📉 [{label}] Progressive trail ({trail_pct*100:.1f}%): {symbol} | {pct:+.2f}% | "
                     f"peak +{peak_profit*100:.1f}%")
            return True, "TRAILING_STOP"

    else:
        # Normal TP for non-scalper trades that haven't hit partial TP
        if label in ("MOONSHOT", "REVERSAL", "PRE_BREAKOUT"):
            # In bull regime: trail instead of fixed TP (captures 3-5× more on runners)
            # Also trail if SL has been ratcheted above entry (micro TP was blocked but price is up)
            sl_ratcheted = trade["sl_price"] > trade["entry_price"] * 1.005
            bull_regime  = _market_regime_mult < 0.95
            if bull_regime or sl_ratcheted:
                # Progressive trail — no ceiling
                if price > trade.get("highest_price", trade["entry_price"]):
                    trade["highest_price"] = price
                atr_pct = trade.get("atr_pct", 0.02)
                peak_profit = (trade.get("highest_price", price) / trade["entry_price"] - 1)
                if peak_profit > 0.02:  # only trail once 2%+ up
                    trail_pct = calc_progressive_trail(peak_profit, atr_pct, strategy=label)
                    trail_sl  = trade["highest_price"] * (1 - trail_pct)
                    if price <= trail_sl:
                        log.info(f"📈 [{label}] Bull trail exit: {symbol} | {pct:+.2f}% | "
                                 f"peak +{peak_profit*100:.1f}% | trail {trail_pct*100:.1f}%")
                        return True, "TRAILING_STOP"
                # Still allow fixed TP as fallback if peak hasn't grown enough
                elif price >= trade["tp_price"]:
                    log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
                    return True, "TAKE_PROFIT"
            else:
                if price >= trade["tp_price"]:
                    log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
                    return True, "TAKE_PROFIT"
        else:
            if price >= trade["tp_price"]:
                log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
                return True, "TAKE_PROFIT"

    # Timeout / momentum decay for MOONSHOT (only if not already risk‑free)
    if label == "MOONSHOT":
        _risk_free = trade.get("micro_tp_hit") or trade.get("partial_tp_hit")
        if not _risk_free and -1.0 <= pct < 0.5 and held_min >= MOONSHOT_TIMEOUT_FLAT_MINS:
            log.info(f"😴 [{label}] Flat timeout: {symbol} | {pct:+.2f}% after {held_min:.0f}min")
            return True, "TIMEOUT"
        if not _risk_free and pct < 5.0 and held_min >= MOONSHOT_TIMEOUT_MARGINAL_MINS:
            # Only exit if progress toward TP is truly marginal (< 35% of target)
            tp_target_pct = trade.get("tp_pct", MOONSHOT_TP_INITIAL) * 100
            marginal_threshold = tp_target_pct * 0.35
            if pct < marginal_threshold:
                log.info(f"⏰ [{label}] Marginal timeout: {symbol} | {pct:+.2f}% "
                         f"(< {marginal_threshold:.1f}% = 35% of {tp_target_pct:.0f}% target) "
                         f"after {held_min:.0f}min")
                return True, "TIMEOUT"
        if not _risk_free and held_min >= MOMENTUM_DECAY_MIN_HELD and pct < 5.0:
            if detect_momentum_decay(symbol):
                log.info(f"📉 [{label}] Momentum decay: {symbol} | {pct:+.2f}%")
                return True, "VOL_COLLAPSE"

    # REVERSAL specials (weak bounce, flat progress) – but only if floor & chase not active
    if label == "REVERSAL" and not trade.get("partial_tp_hit") and not trade.get("trailing_active"):
        if held_min >= REVERSAL_FLAT_MINS and pct >= 0:
            tp_range = trade["tp_price"] - trade["entry_price"]
            if tp_range > 0:
                progress = (price - trade["entry_price"]) / tp_range
                if progress < REVERSAL_FLAT_PROGRESS:
                    log.info(f"😴 [{label}] Flat-progress exit: {symbol} | "
                             f"{pct:+.2f}% | progress {progress*100:.0f}% "
                             f"< {REVERSAL_FLAT_PROGRESS*100:.0f}% after {held_min:.0f}min")
                    return True, "FLAT_EXIT"
        if (held_min >= REVERSAL_WEAK_BOUNCE_MINS
                and pct < REVERSAL_WEAK_BOUNCE_PCT
                and trade["sl_price"] < trade["entry_price"]):
            trade["sl_price"] = trade["entry_price"]
            log.info(f"🔄 [{label}] Weak bounce after {held_min:.0f}min — SL moved to entry")

    log.info(f"👀 [{label}] {symbol} | {pct:+.2f}% | {held_min:.0f}min | "
             f"High: {((trade['highest_price']/trade['entry_price'])-1)*100:.2f}%")
    return False, ""

def execute_partial_tp(trade, micro: bool = False) -> bool:
    label   = trade["label"]
    symbol  = trade["symbol"]
    ratio   = (trade.get("micro_tp_ratio", MOONSHOT_MICRO_TP_RATIO) if micro
               else trade.get("partial_tp_ratio", 0.5))
    reason_tag = "MICRO_TP" if micro else "PARTIAL_TP"
    min_qty, step_size, min_notional, _ = get_symbol_rules(symbol)
    d_step  = Decimal(str(step_size))

    # ── Step 1: Get the TRUE quantity we hold ──────────────────────
    if PAPER_TRADE:
        actual_qty = trade["qty"]
    else:
        actual_qty = get_sellable_qty(symbol, fallback_qty=trade["qty"])
        if actual_qty <= 0:
            log.warning(f"[{label}] Partial TP: no sellable balance for {symbol} — skipping")
            if micro: trade["micro_tp_hit"] = True
            else:     trade["partial_tp_hit"] = True
            return True

    d_actual = Decimal(str(actual_qty))

    # ── Step 2: Work BACKWARDS from remainder ──────────────────────
    # Calculate desired remaining, round to step_size
    desired_remaining = float((d_actual * (1 - Decimal(str(ratio))) / d_step)
                              .to_integral_value(rounding=ROUND_DOWN) * d_step)

    # Check if remainder is sellable — if not, sell everything
    current_price = None
    try:
        current_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception:
        pass

    sell_all = False
    if desired_remaining < min_qty:
        sell_all = True
        log.info(f"[{label}] Remainder {desired_remaining} < min_qty {min_qty} — selling 100%")
    elif current_price and desired_remaining * current_price < DUST_THRESHOLD:
        sell_all = True
        log.info(f"[{label}] Remainder would be dust "
                 f"(${desired_remaining * current_price:.2f}) — selling 100%")
    elif current_price and min_notional > 0 and desired_remaining * current_price < min_notional:
        sell_all = True
        log.info(f"[{label}] Remainder below min_notional — selling 100%")

    if sell_all:
        partial_qty   = actual_qty
        remaining_qty = 0.0
        reason_tag    = "FULL_CLOSE"
    else:
        # partial_qty = total - valid_remainder (guaranteed clean math)
        remaining_qty = desired_remaining
        partial_qty   = float((d_actual - Decimal(str(remaining_qty))))
        # Re-round partial to step_size
        partial_qty   = float((Decimal(str(partial_qty)) / d_step)
                              .to_integral_value(rounding=ROUND_DOWN) * d_step)

    # Final sanity: partial must be >= min_qty
    if partial_qty < min_qty:
        log.warning(f"[{label}] {reason_tag} skipped — partial_qty {partial_qty} < min {min_qty}")
        if micro: trade["micro_tp_hit"] = True
        else:     trade["partial_tp_hit"] = True
        return True

    # ── Step 3: Execute the sell ───────────────────────────────────
    if label == "MOONSHOT" and reason_tag in ("PARTIAL_TP", "MICRO_TP", "FULL_CLOSE"):
        timeout = 1.0
        max_retries = 2
    else:
        timeout = CHASE_LIMIT_TIMEOUT
        max_retries = CHASE_LIMIT_RETRIES

    partial_sell_id  = None
    partial_sold_at_ms = int(time.time() * 1000)
    if not PAPER_TRADE:
        if label == "SCALPER" and trade.get("tp_order_id"):
            cancel_order(symbol, trade["tp_order_id"], label)
            trade["tp_order_id"] = None
        result = chase_limit_sell(symbol, partial_qty, label, tag=reason_tag,
                                  timeout=timeout, max_retries=max_retries)
        partial_sell_id = result.get("orderId") if result else None
        if not result:
            log.error(f"🚨 [{label}] Partial TP sell failed.")
            return False

    # ── Step 4: Sync trade["qty"] with ACTUAL exchange balance ─────
    if not PAPER_TRADE:
        time.sleep(1.0)  # let MEXC settle and index fills
        synced_qty = get_sellable_qty(symbol)
        if synced_qty >= 0:
            remaining_qty = synced_qty
            log.info(f"[{label}] Post-sell sync: exchange has {synced_qty} {symbol.replace('USDT','')}")
    trade["qty"] = remaining_qty

    # ── Step 5: Record P&L (using entry_price, not budget_used) ────
    partial_fills = {}
    if not PAPER_TRADE:
        sell_ids = {partial_sell_id} if partial_sell_id else None
        partial_fills = get_actual_fills(
            symbol, since_ms=partial_sold_at_ms, retries=4,
            buy_order_id=None, sell_order_ids=sell_ids,
        )
    try:
        ticker_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception:
        ticker_price = (trade.get("micro_tp_price") if micro
                        else trade.get("partial_tp_price", trade["entry_price"]))
    actual_entry = partial_fills.get("avg_buy_price")  or trade["entry_price"]
    actual_exit  = partial_fills.get("avg_sell_price") or ticker_price
    fee_usdt     = partial_fills.get("fee_usdt", 0.0)
    fills_used   = bool(partial_fills.get("avg_sell_price"))
    # P&L based on actual entry price × qty (not budget_used which drifts)
    partial_cost = round(actual_entry * partial_qty, 4)
    partial_rev  = partial_fills.get("revenue_usdt") or round(actual_exit * partial_qty, 4)
    partial_pnl  = round(partial_rev - partial_cost - fee_usdt, 4)
    partial_pct  = round((actual_exit / actual_entry - 1) * 100, 4) if actual_entry > 0 else 0.0
    trade_history.append({
        **{k: v for k, v in trade.items() if not k.startswith("_")},
        "qty":           partial_qty,
        "budget_used":   partial_cost,
        "exit_price":    actual_exit,
        "exit_ticker":   ticker_price,
        "exit_reason":   reason_tag,
        "closed_at":     datetime.now(timezone.utc).isoformat(),
        "fee_usdt":      fee_usdt,
        "cost_usdt":     partial_cost,
        "revenue_usdt":  partial_rev,
        "pnl_pct":       partial_pct,
        "pnl_usdt":      partial_pnl,
        "fills_used":    fills_used,
        "is_partial":    True,
    })

    # ── Step 6: Update trade state ─────────────────────────────────
    # budget_used tracks entry_price × remaining_qty (stays accurate)
    trade["budget_used"] = round(actual_entry * remaining_qty, 4)
    if label in ("MOONSHOT", "REVERSAL", "PRE_BREAKOUT"):
        activate_floor_and_chase(trade, actual_exit)
        trade["sl_price"] = trade["entry_price"]
    else:
        trade["sl_price"] = trade["entry_price"]
    if micro:
        trade["micro_tp_hit"] = True
    else:
        trade["partial_tp_hit"] = True
    trade["bought_at_ms"] = partial_sold_at_ms
    if label == "SCALPER" and not PAPER_TRADE and remaining_qty > 0:
        new_tp_id = place_limit_sell(symbol, remaining_qty, trade["tp_price"],
                                     label, tag="TP_REMAINDER")
        trade["tp_order_id"] = new_tp_id
        if new_tp_id:
            log.info(f"[SCALPER] Re-placed TP limit for {remaining_qty} @ ${trade['tp_price']:.6f}")
        else:
            log.warning(f"[SCALPER] TP re-place failed for {symbol} — remainder monitored by bot")
    save_state()

    # ── Step 7: Telegram notification ──────────────────────────────
    mode       = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    fills_note = "✅" if fills_used else "⚠️ est"
    sell_pct   = round(partial_qty / (partial_qty + remaining_qty) * 100) if (partial_qty + remaining_qty) > 0 else 100
    icon       = "🎯μ" if micro else {"MOONSHOT":"🌙","REVERSAL":"🔄","PRE_BREAKOUT":"🔮"}.get(label, "🎯")
    stage_str  = "μTP" if micro else ("FULL" if reason_tag == "FULL_CLOSE" else "½TP")
    log.info(f"{icon} [{label}] {stage_str} {symbol}: sold {partial_qty} @ ${actual_exit:.6f} "
             f"(entry ${actual_entry:.6f}) P&L {partial_pct:+.2f}% (${partial_pnl:+.2f}) | "
             f"Remaining: {remaining_qty}")
    # Next action line
    if remaining_qty <= 0:
        next_line = "Position closed ✅"
    elif trade.get("trailing_active"):
        next_line = (f"🔒 Floor ${trade['hard_floor_price']:.6f} | "
                     f"Trail ${trade['trailing_stop_price']:.6f}")
    else:
        next_line = f"🔒 SL → entry ${trade['entry_price']:.6f}"
    telegram(
        f"{icon} <b>{stage_str} — {label} {symbol}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Sold {partial_qty} ({sell_pct}%) @ <b>${actual_exit:.6f}</b> [{fills_note}]\n"
        f"P&L <b>{partial_pct:+.2f}% (${partial_pnl:+.2f})</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{next_line}"
    )
    return True

def close_position(trade, reason) -> bool:
    label  = trade["label"]
    symbol = trade["symbol"]
    needs_sell = (
        (label in ("MOONSHOT", "REVERSAL", "PRE_BREAKOUT")) or
        (label == "SCALPER" and reason in ("STOP_LOSS","TRAILING_STOP","TIMEOUT","FLAT_EXIT","ROTATION","VOL_COLLAPSE","PROTECT_STOP","MAJOR_PARTIAL_TP")) or
        (label == "TRINITY" and reason in ("STOP_LOSS","TIMEOUT"))
    )
    sell_order_id = None

    # --- DUST HANDLING: Check if remaining position is too small to sell ---
    current_price = None
    try:
        current_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception:
        pass
    if current_price is not None:
        remaining_notional = trade["qty"] * current_price
        if remaining_notional < DUST_THRESHOLD:
            dust_cost = trade.get("budget_used", 0)
            dust_pnl  = round(remaining_notional - dust_cost, 4) if dust_cost > 0 else 0.0
            dust_pct  = round(dust_pnl / dust_cost * 100, 4) if dust_cost > 0 else 0.0
            log.info(f"🧹 [{label}] Dust position: {symbol} qty={trade['qty']:.6f} value=${remaining_notional:.2f} (< ${DUST_THRESHOLD}) — marking as closed")
            trade_history.append({
                **{k: v for k, v in trade.items() if not k.startswith("_")},
                "exit_price":   current_price,
                "exit_ticker":  current_price,
                "exit_reason":  "DUST",
                "closed_at":    datetime.now(timezone.utc).isoformat(),
                "fee_usdt":     0.0,
                "cost_usdt":    dust_cost,
                "revenue_usdt": round(remaining_notional, 4),
                "pnl_pct":      dust_pct,
                "pnl_usdt":     dust_pnl,
                "fills_used":   False,
                "note":         f"Position too small (< ${DUST_THRESHOLD}) – marked as closed",
            })
            # Send a Telegram notification for dust closure
            telegram(f"🧹 <b>Dust — {label} {symbol}</b> | ${remaining_notional:.2f} | auto-closed")
            return True
    # --- End dust handling ---

    if needs_sell and not PAPER_TRADE:
        tp_order_id = trade.get("tp_order_id")
        if label in ("SCALPER", "TRINITY") and tp_order_id:
            cancel_order(symbol, tp_order_id, label)
            for _ in range(3):
                time.sleep(0.3)
                if tp_order_id not in get_open_order_ids(symbol):
                    break
            trade["tp_order_id"] = None

        # For defensive exits: cancel all open orders, then market sell
        defensive_reasons = ("STOP_LOSS", "TRAILING_STOP", "TIMEOUT", "FLAT_EXIT", "ROTATION", "VOL_COLLAPSE", "PROTECT_STOP")
        if reason in defensive_reasons:
            # Cancel all open orders to unlock balance
            cancel_all_orders(symbol)
            time.sleep(1.5)          # give MEXC time to unlock funds
            # Market sell with fresh balance on each attempt
            market_attempts = 5
            for attempt in range(market_attempts):
                # Fetch actual balance and round to step_size on EVERY attempt
                sell_qty = get_sellable_qty(symbol, fallback_qty=trade["qty"])
                if sell_qty <= 0:
                    # Position already gone or below min_qty
                    log.info(f"🧹 [{label}] No sellable qty for {symbol} — position closed or dust")
                    sell_order_id = "already_closed"
                    break
                try:
                    result = private_post("/api/v3/order", {
                        "symbol": symbol, "side": "SELL", "type": "MARKET", "quantity": str(sell_qty)
                    })
                    sell_order_id = result.get("orderId")
                    log.info(f"✅ [{label}] Market sell (defensive) attempt {attempt+1}/{market_attempts}: qty={sell_qty} {result}")
                    # Wait a moment for order to process
                    time.sleep(1)
                    remaining = get_asset_balance(symbol)
                    if current_price is not None:
                        remaining_notional = remaining * current_price
                        if remaining_notional < DUST_THRESHOLD:
                            log.info(f"✅ [{label}] Market sell succeeded – remaining ${remaining_notional:.2f} (dust)")
                            break
                    if remaining < sell_qty * 0.01:
                        log.info(f"✅ [{label}] Position {symbol} closed via market sell")
                        break
                    else:
                        log.info(f"⚠️ [{label}] Market sell attempt {attempt+1} still has {remaining:.4f} – retrying")
                except requests.exceptions.HTTPError as e:
                    try: body = e.response.json()
                    except Exception: body = {}
                    err_code = body.get("code") if isinstance(body, dict) else None
                    if err_code == 30005:
                        log.info(f"✅ [{label}] Order already closed (code 30005) for {symbol} — assuming closed")
                        sell_order_id = "already_closed"
                        break
                    elif err_code in (10006, 2005):
                        log.info(f"🧹 [{label}] Order size too small for {symbol} – treating as dust")
                        break
                    elif err_code == 400 or (isinstance(body, dict) and "scale" in str(body.get("msg", "")).lower()):
                        # Quantity precision error — will re-fetch on next attempt
                        log.warning(f"⚠️ [{label}] Qty precision error for {symbol} (qty={sell_qty}): {body} — will re-fetch balance")
                    else:
                        # Check if we should send an alert (de‑duplication)
                        now = time.time()
                        last_alert = _last_error_time.get(symbol, 0)
                        if now - last_alert > ERROR_ALERT_COOLDOWN:
                            _last_error_time[symbol] = now
                            log.error(f"🚨 [{label}] Market sell defensive attempt {attempt+1} failed: {e}")
                            telegram(f"🚨 <b>Sell retry</b> {label} {symbol} | "
                                     f"{attempt+1}/{market_attempts} | {str(body)[:100]}")
                        else:
                            log.debug(f"🚨 [{label}] Market sell defensive attempt {attempt+1} failed (alert suppressed): {e}")
                    sell_order_id = None
                except Exception as e:
                    log.error(f"🚨 [{label}] Market sell defensive attempt {attempt+1} failed: {e}")
                    sell_order_id = None

                if attempt < market_attempts - 1:
                    time.sleep(1)  # short delay between retries

            # After all attempts, check remaining balance
            final_remaining = get_asset_balance(symbol)
            if current_price is not None:
                final_notional = final_remaining * current_price
                if final_notional >= DUST_THRESHOLD:
                    log.error(f"🚨 [{label}] Could not close {symbol} after {market_attempts} attempts! "
                              f"Remaining {final_remaining:.4f} (${final_notional:.2f})")
                    now = time.time()
                    last_alert = _last_error_time.get(symbol, 0)
                    if now - last_alert > ERROR_ALERT_COOLDOWN:
                        _last_error_time[symbol] = now
                        telegram(f"🚨 <b>Close failed!</b> {label} {symbol}\n"
                                 f"{reason} | {final_remaining:.4f} (~${final_notional:.2f}) remaining")
                    return False
                # Dust remaining — fall through to normal close notification
                log.info(f"🧹 [{label}] {symbol} dust remaining (${final_notional:.2f}) — recording close")
            else:
                if final_remaining > trade["qty"] * 0.01:
                    log.error(f"🚨 [{label}] Could not close {symbol} after {market_attempts} attempts! "
                              f"Remaining {final_remaining:.4f}")
                    now = time.time()
                    last_alert = _last_error_time.get(symbol, 0)
                    if now - last_alert > ERROR_ALERT_COOLDOWN:
                        _last_error_time[symbol] = now
                        telegram(f"🚨 <b>Close failed!</b> {label} {symbol}\n"
                                 f"{reason} | {final_remaining:.4f} remaining")
                    return False
                # Success — fall through to normal close notification

        # For non‑defensive exits: use chase limit, but ensure full closure
        else:
            # For moonshot take profits, use short timeout
            if label == "MOONSHOT" and reason == "TAKE_PROFIT":
                timeout = 1.0
                max_retries = 2
            else:
                timeout = CHASE_LIMIT_TIMEOUT
                max_retries = CHASE_LIMIT_RETRIES

            # Attempt to sell the whole position with chase limit
            # Use get_sellable_qty to ensure proper step_size rounding
            remaining_qty = get_sellable_qty(symbol, fallback_qty=trade["qty"])
            if remaining_qty <= 0:
                log.info(f"✅ [{label}] No sellable qty for {symbol} — position already closed")
                sell_order_id = "already_closed"
            else:
                success = False
                max_loops = 3  # prevent infinite loop
                for loop in range(max_loops):
                    result = chase_limit_sell(symbol, remaining_qty, label, tag=reason,
                                              timeout=timeout, max_retries=max_retries)
                    if result is None:
                        log.error(f"🚨 [{label}] Chase limit sell failed – result is None")
                        return False

                    sell_order_id = result.get("orderId")
                    if not sell_order_id:
                        log.error(f"🚨 [{label}] Chase limit sell returned no orderId")
                        return False

                    # Give the order a moment to fill
                    time.sleep(1)

                    # Check how much is still left — use get_sellable_qty for proper rounding
                    remaining_qty = get_sellable_qty(symbol)
                    if remaining_qty <= 0:
                        log.info(f"✅ [{label}] Position {symbol} closed via chase limit sell")
                        success = True
                        break

                    remaining_raw = get_asset_balance(symbol)
                    if current_price is not None:
                        remaining_notional = remaining_raw * current_price
                        if remaining_notional < DUST_THRESHOLD:
                            log.info(f"🧹 [{label}] Dust after chase limit sell – treating as closed")
                            success = True
                            break

                    # Partial fill – cancel remaining orders, market sell with fresh qty
                    log.warning(f"⚠️ [{label}] Chase partially filled. "
                                f"Remaining {remaining_qty} – switching to market sell.")
                    cancel_all_orders(symbol)
                    time.sleep(0.5)
                    sell_qty = get_sellable_qty(symbol)
                    if sell_qty <= 0:
                        log.info(f"✅ [{label}] No sellable qty after cancel — position closed")
                        success = True
                        break
                    try:
                        market_result = private_post("/api/v3/order", {
                            "symbol": symbol, "side": "SELL", "type": "MARKET",
                            "quantity": str(sell_qty)
                        })
                        if market_result:
                            log.info(f"✅ [{label}] Market sell completed the position: {market_result}")
                            success = True
                            break
                    except Exception as e:
                        log.error(f"🚨 [{label}] Market sell failed after partial fill: {e}")
                    break  # don't loop further on market sell failure

                if not success:
                    log.error(f"🚨 [{label}] Failed to close position {symbol} after all attempts.")
                    return False

    exit_fills = {}
    if not PAPER_TRADE:
        bought_at_ms  = trade.get("bought_at_ms", int(time.time() * 1000) - 86400_000)
        buy_order_id  = trade.get("buy_order_id")
        known_sell_ids = set()
        if trade.get("tp_order_id"):
            known_sell_ids.add(trade["tp_order_id"])
        if sell_order_id and sell_order_id != "already_closed":
            known_sell_ids.add(sell_order_id)
        retries    = 5 if (reason == "TAKE_PROFIT" and label in ("SCALPER", "TRINITY")) else 3
        exit_fills = get_actual_fills(
            symbol, since_ms=bought_at_ms, retries=retries,
            buy_order_id=buy_order_id,
            sell_order_ids=known_sell_ids or None,
        )
    try:
        ticker_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception:
        ticker_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]
    actual_entry  = exit_fills.get("avg_buy_price")   or trade["entry_price"]
    actual_exit   = exit_fills.get("avg_sell_price")  or ticker_price
    fee_usdt      = exit_fills.get("fee_usdt",  0.0)
    cost_usdt     = exit_fills.get("cost_usdt") or (actual_entry * trade["qty"])
    revenue_usdt  = exit_fills.get("revenue_usdt") or (actual_exit * trade["qty"])
    pnl_usdt = round(revenue_usdt - cost_usdt - fee_usdt, 4)
    pnl_pct  = round(pnl_usdt / cost_usdt * 100, 4) if cost_usdt > 0 else 0.0
    if exit_fills.get("avg_sell_price"):
        log.info(f"[{label}] Fills: entry=${actual_entry:.6f} exit=${actual_exit:.6f} "
                 f"fees=${fee_usdt:.4f} P&L=${pnl_usdt:+.4f} ({pnl_pct:+.2f}%)")
    else:
        log.info(f"[{label}] Ticker exit ${ticker_price:.6f} (myTrades unavailable) "
                 f"P&L=${pnl_usdt:+.4f} ({pnl_pct:+.2f}%)")
    peak_price    = trade.get("highest_price", actual_entry)
    peak_profit   = (peak_price / actual_entry - 1) if actual_entry > 0 else 0.0
    actual_profit = (actual_exit / actual_entry - 1) if actual_entry > 0 else 0.0
    giveback_ratio = (
        (peak_profit - actual_profit) / peak_profit
        if peak_profit > 0.001 else 0.0
    )
    # Cap giveback at 100% for display
    giveback_display = giveback_ratio
    if giveback_ratio > 1.0:
        giveback_display = 1.0
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
        "highest_price":    peak_price,
        "peak_profit_pct":  round(peak_profit * 100, 4),
        "giveback_ratio":   round(giveback_ratio, 4),
        "move_maturity":    trade.get("move_maturity"),
        "adaptive_offset":  _adaptive_offsets.get(label, 0.0),
    })
    if giveback_ratio > 0 and peak_profit > 0.005:
        log.info(f"📊 [{label}] Giveback: peak +{peak_profit*100:.1f}% → "
                 f"exit {actual_profit*100:+.1f}% | gave back {giveback_ratio*100:.0f}%"
                 + (f" ⚠️ trail too wide" if giveback_ratio > GIVEBACK_TARGET_HIGH else ""))
    global _consecutive_losses, _win_rate_pause_until, _strategy_loss_streaks, _strategy_paused_until
    if label == "SCALPER":
        if pnl_pct <= 0:
            _consecutive_losses += 1
        else:
            _consecutive_losses = 0
    # P6: Per-strategy loss streak (Trinity/Reversal crash guard)
    if label in ("TRINITY", "REVERSAL"):
        if pnl_pct <= 0:
            _strategy_loss_streaks[label] = _strategy_loss_streaks.get(label, 0) + 1
            streak = _strategy_loss_streaks[label]
            if streak >= STRATEGY_LOSS_STREAK_MAX:
                pause_until = time.time() + STRATEGY_LOSS_STREAK_MINS * 60
                _strategy_paused_until[label] = pause_until
                log.info(f"🛑 [{label}] {streak} consecutive losses — paused for {STRATEGY_LOSS_STREAK_MINS//60}h")
                telegram(f"🛑 <b>{label} paused</b> | {streak}L streak | {STRATEGY_LOSS_STREAK_MINS//60}h cooldown")
        else:
            _strategy_loss_streaks[label] = 0
    try:
        update_adaptive_thresholds()
        rebalance_budgets()
    except Exception as e:
        log.debug(f"Adaptive learning update failed: {e}")
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
                f"🛑 <b>Win-rate CB</b> | {recent_win_rate*100:.0f}% WR over {WIN_RATE_CB_WINDOW}t\n"
                f"Entries paused {WIN_RATE_CB_PAUSE_MINS}min. Open positions monitored."
            )
            save_state()
    full_trades = [t for t in trade_history if not t.get("is_partial")]
    wins        = [t for t in full_trades if t["pnl_pct"] > 0]
    win_rate    = len(wins) / len(full_trades) * 100 if full_trades else 0
    total_pnl   = sum(t["pnl_usdt"] for t in trade_history)  # includes partials (real money)
    partial_count = sum(1 for t in trade_history if t.get("is_partial"))
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
        "MICRO_TP":      ("🎯μ","Micro Take Profit"),
        "PROTECT_STOP":  ("🛡️","Protection Stop"),
        "MICRO_HWM":     ("🛡️","Micro‑Cap HWM"),
        "DYN_HWM":       ("🛡️","Dynamic HWM"),
        "MAJOR_PARTIAL_TP": ("🎯","Major Partial Fill"),
        "DUST":          ("🧹","Dust Position"),
        "FLOOR_OR_TRAIL":("🛡️","Floor & Trail"),
    }
    emoji, reason_label = icons.get(reason, ("✅", reason))
    fills_note = "✅" if exit_fills.get("avg_sell_price") else "⚠️ est"
    peak_line  = (f"Peak +{peak_profit*100:.1f}% (gave back {giveback_display*100:.0f}%)\n"
                  if peak_profit > 0.005 else "")
    telegram(
        f"{emoji} <b>{reason_label} — {label} {symbol}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"${actual_entry:.6f} → <b>${actual_exit:.6f}</b> [{fills_note}]\n"
        f"P&L <b>{pnl_pct:+.2f}% (${pnl_usdt:+.2f})</b>"
        + (f" | Fees ${fee_usdt:.4f}" if fee_usdt > 0 else "") + "\n"
        f"{peak_line}"
        f"━━━━━━━━━━━━━━━\n"
        f"{len(full_trades)}t | WR {win_rate:.0f}% | Total <b>${total_pnl:+.2f}</b>"
    )
    log.info(f"📈 Closed {symbol} [{reason}] {pnl_pct:+.2f}% | Win:{win_rate:.0f}% P&L:${total_pnl:+.2f}")
    save_state()
    return True

def _trade_price_pct(trade: dict) -> tuple[float | None, float | None]:
    try:
        px = ws_price(trade["symbol"]) or float(
            public_get("/api/v3/ticker/price", {"symbol": trade["symbol"]})["price"]
        )
        pct = (px - trade["entry_price"]) / trade["entry_price"] * 100
        return px, pct
    except Exception:
        return None, None

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
    # Market regime label
    mult = _market_regime_mult
    if mult > 1.30: regime_label = "🔴 CRASH"
    elif mult > 1.10: regime_label = "🟠 BEAR"
    elif mult > 0.95: regime_label = "⚪ SIDEWAYS"
    elif mult > 0.80: regime_label = "🟢 BULL"
    else: regime_label = "🚀 STRONG BULL"
    session_pnl = sum(t.get("pnl_usdt", 0) for t in trade_history)
    scalper_lines = []
    for t in scalper_trades:
        _, pct = _trade_price_pct(t)
        scalper_lines.append(f"  🟢 {t['symbol']} {pct:+.2f}%" if pct is not None else f"  🟢 {t['symbol']}")
    if not scalper_trades:
        scalper_lines.append(f"  {'👀 ' + last_top_scalper['symbol'] if last_top_scalper else 'scanning...'}")
    alt_lines = []
    for t in alt_trades:
        _, pct = _trade_price_pct(t)
        ic = {"MOONSHOT":"🌙","REVERSAL":"🔄","TRINITY":"🔱","PRE_BREAKOUT":"🔮"}.get(t['label'],"•")
        fc = " 🔒" if t.get("trailing_active") else ""
        alt_lines.append(f"  {ic} {t['symbol']} {pct:+.2f}%{fc}" if pct is not None else f"  {ic} {t['symbol']}")
    if not alt_trades:
        alt_lines.append(f"  {'👀 ' + last_top_alt['symbol'] if last_top_alt else 'scanning...'}")
    total_value = balance
    for t in scalper_trades + alt_trades:
        px, _ = _trade_price_pct(t)
        total_value += px * t["qty"] if px else t.get("budget_used", 0)
    moon_gate = "✅" if _moonshot_gate_open else "⛔"
    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{regime_label} | BTC {_btc_ema_gap_macro*100:+.1f}% | Moon {moon_gate}\n"
        f"💰 ${balance:.2f} free | ${total_value:.2f} total | P&L ${session_pnl:+.2f}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Scalper ({len(scalper_trades)}/{SCALPER_MAX_TRADES}):\n"
        + "\n".join(scalper_lines) + "\n"
        + f"Alt ({len(alt_trades)}):\n"
        + "\n".join(alt_lines) + "\n"
        + f"━━━━━━━━━━━━━━━\n"
        f"Today: {trades_today}t | <i>/status /pnl /config</i>"
    )

def convert_dust():
    if PAPER_TRADE:
        return
    try:
        balances = private_get("/api/v3/account").get("balances", [])
        candidates = {
            b["asset"]: float(b.get("free", 0))
            for b in balances
            if b["asset"] not in ("USDT", "MX") and float(b.get("free", 0)) > 0
        }
        if not candidates:
            log.info("🧹 Dust sweep: nothing to convert.")
            return
        try:
            all_prices = {p["symbol"]: float(p["price"])
                          for p in public_get("/api/v3/ticker/price")}
        except Exception:
            all_prices = {}
        dust = []
        for asset, free in candidates.items():
            price = all_prices.get(f"{asset}USDT", 0.0)
            if price > 0 and 0 < free * price < 1.0:
                dust.append(asset)
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

def ask_haiku(prompt: str, system: str = "", max_tokens: int = 500) -> str:
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
    if not SENTIMENT_ENABLED or not today_trades:
        return ""
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
            f"signal={t.get('entry_signal','?')} "
            f"entry={t.get('entry_price',0):.6f} exit={t.get('exit_price',0):.6f} "
            f"pnl={t.get('pnl_pct',0):+.2f}% (${t.get('pnl_usdt',0):+.2f}) "
            f"reason={t.get('exit_reason','?')} "
            f"score={t.get('score',0):.0f} rsi={t.get('rsi',0):.0f} "
            f"peak={t.get('peak_profit_pct',0):+.1f}% giveback={t.get('giveback_ratio',0)*100:.0f}% "
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
        "• Entry signal patterns: which signals (CROSSOVER, VOL_SPIKE, OVERSOLD, TREND) are winning vs losing?\n"
        "• Giveback analysis: are we giving back too much peak profit? Note any trades with >50% giveback\n"
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

def _fetch_fills_since(symbols: list, since_ms: int) -> dict:
    all_fills = []
    for sym in symbols:
        try:
            fills = private_get("/api/v3/myTrades",
                                {"symbol": sym, "startTime": since_ms, "limit": 1000})
            if fills:
                all_fills.extend(fills)
        except Exception:
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
    convert_dust()
    if PAPER_TRADE:
        if not trade_history:
            telegram(f"📅 <b>Daily Summary</b> [{mode}]\n━━━━━━━━━━━━━━━\nNo trades today.")
            return
        def block(lbl):
            ts = [t for t in trade_history if t.get("label") == lbl]
            if not ts: return ""
            wins = [t for t in ts if t["pnl_pct"] > 0]
            return (f"\n{lbl}: {len(ts)}t {len(wins)}W "
                    f"${sum(t['pnl_usdt'] for t in ts):+.2f}")
        total = sum(t["pnl_usdt"] for t in trade_history)
        telegram(f"📅 <b>Daily</b> [{mode}]\n━━━━━━━━━━━━━━━"
                 + block("SCALPER") + block("MOONSHOT") + block("REVERSAL")
                 + block("TRINITY") + block("PRE_BREAKOUT")
                 + f"\n━━━━━━━━━━━━━━━\nP&L <b>${total:+.2f}</b> | Bal <b>${balance:.2f}</b>")
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
        telegram(f"📅 <b>Daily</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
                 f"{len(buys)}B/{len(sells)}S | {syms}\n"
                 f"Net {emoji} <b>${net:+.2f}</b> | Bal <b>${balance:.2f}</b>")
    except Exception as e:
        log.error(f"Daily summary failed: {e}")
    try:
        today_trades = [t for t in trade_history if t.get("closed_at","")[:10] == today]
        journal = generate_daily_journal(today_trades, balance)
        if journal:
            telegram(journal[:4000])
    except Exception as e:
        log.debug(f"Daily journal failed: {e}")

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
        msg = (f"{emoji} <b>Weekly</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
               f"{pnl['total']}t ({pnl.get('wins',0)}W/{pnl.get('losses',0)}L) | "
               f"WR {wr} | <b>${pnl['pnl_usdt']:+.2f}</b>\n"
               f"Bal <b>${balance:.2f}</b>")
        if pnl.get("best"):  msg += f"\n🏆 {pnl['best']['symbol']} {pnl['best']['pnl_pct']:+.2f}%"
        if pnl.get("worst"): msg += f" | 💀 {pnl['worst']['symbol']} {pnl['worst']['pnl_pct']:+.2f}%"
        return msg
    return (f"{emoji} <b>Weekly</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
            f"{pnl['total']} round trips | <b>${pnl['pnl_usdt']:+.2f}</b>\n"
            f"Bal <b>${balance:.2f}</b>")

def send_weekly_summary(balance: float):
    global last_weekly_summary
    now  = datetime.now(timezone.utc)
    week = f"{now.isocalendar()[0]}-W{now.isocalendar()[1]:02d}"
    if last_weekly_summary == week or now.weekday() != 0 or now.hour != 0:
        return
    last_weekly_summary = week
    telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))

def _cmd_status(balance: float):
    mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    # Market regime classification
    mult = _market_regime_mult
    btc_gap = _btc_ema_gap_macro
    if mult > 1.30:
        regime_label = "🔴 CRASH"
    elif mult > 1.10:
        regime_label = "🟠 BEAR"
    elif mult > 0.95:
        regime_label = "⚪ SIDEWAYS"
    elif mult > 0.80:
        regime_label = "🟢 BULL"
    else:
        regime_label = "🚀 STRONG BULL"
    session_pnl = sum(t.get("pnl_usdt", 0) for t in trade_history)
    lines = [f"📋 <b>Status</b> [{mode}]\n━━━━━━━━━━━━━━━"]
    lines.append(f"Market: <b>{regime_label}</b> (×{mult:.2f}) | BTC EMA: {btc_gap*100:+.1f}%")
    lines.append(f"Session: <b>${session_pnl:+.2f}</b> | Moon gate: {'✅' if _moonshot_gate_open else '⛔'}")
    # Strategy pauses
    pauses = []
    if _session_loss_paused_until > time.time():
        pauses.append(f"📛 All entries paused ({(_session_loss_paused_until - time.time())/60:.0f}min)")
    for lbl in ("TRINITY", "REVERSAL"):
        until = _strategy_paused_until.get(lbl, 0)
        if until > time.time():
            pauses.append(f"🛑 {lbl} paused ({(until - time.time())/60:.0f}min)")
    if pauses:
        lines.extend(pauses)
    lines.append("━━━━━━━━━━━━━━━")
    for t in scalper_trades:
        _, pct = _trade_price_pct(t)
        if pct is not None:
            lines.append(f"🟢 {t['symbol']} | {pct:+.2f}% | "
                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
        else:
            lines.append(f"🟢 {t['symbol']} (unavailable)")
    if not scalper_trades:
        lines.append("Scalper: scanning...")
    for t in alt_trades:
        _, pct = _trade_price_pct(t)
        if pct is not None:
            icon = {"MOONSHOT":"🌙","REVERSAL":"🔄","TRINITY":"🔱","PRE_BREAKOUT":"🔮"}.get(t['label'], "•")
            if t.get("trailing_active") and t.get("hard_floor_price"):
                sl_display = (f"Floor: ${t['hard_floor_price']:.6f} | "
                              f"Trail: ${t['trailing_stop_price']:.6f}")
            else:
                sl_display = f"SL: ${t['sl_price']:.6f}"
            lines.append(f"{icon} <b>{t['symbol']}</b> | {pct:+.2f}% | "
                         f"TP: ${t['tp_price']:.6f} | {sl_display}")
        else:
            lines.append(f"{t['label']}: {t['symbol']} (unavailable)")
    if not alt_trades:
        lines.append("Alt: scanning...")
    lines.append(f"━━━━━━━━━━━━━━━\nBalance: <b>${balance:.2f} USDT</b>")
    telegram("\n".join(lines))

def _compute_metrics(trades: list, since_label: str = "all-time") -> dict:
    full = [t for t in trades if not t.get("is_partial")]
    if not full:
        return {}
    pnls      = [t["pnl_pct"] for t in full]
    pnls_usdt = [t["pnl_usdt"] for t in full]
    wins      = [p for p in pnls if p > 0]
    losses    = [p for p in pnls if p <= 0]
    wins_usdt = [p for p in pnls_usdt if p > 0]
    losses_usdt = [p for p in pnls_usdt if p <= 0]
    equity   = 0.0
    peak     = 0.0
    max_dd   = 0.0
    for p in pnls_usdt:
        equity += p
        peak    = max(peak, equity)
        dd      = peak - equity
        max_dd  = max(max_dd, dd)
    n = len(pnls)
    mean_pnl = sum(pnls) / n
    if n > 1:
        variance = sum((p - mean_pnl) ** 2 for p in pnls) / (n - 1)
        std_pnl  = variance ** 0.5
        sharpe   = (mean_pnl / std_pnl * (n ** 0.5)) if std_pnl > 0 else 0.0
    else:
        sharpe = 0.0
    profit_factor = (sum(wins) / abs(sum(losses))) if losses and sum(losses) != 0 else float("inf")
    best  = max(full, key=lambda t: t["pnl_pct"])
    worst = min(full, key=lambda t: t["pnl_pct"])
    # Expectancy: avg $ per trade (the real measure of bot quality)
    expectancy = sum(pnls_usdt) / n if n > 0 else 0.0
    # Average hold time
    hold_times = []
    for t in full:
        try:
            opened = datetime.fromisoformat(t["opened_at"])
            closed = datetime.fromisoformat(t["closed_at"])
            if opened.tzinfo is None: opened = opened.replace(tzinfo=timezone.utc)
            if closed.tzinfo is None: closed = closed.replace(tzinfo=timezone.utc)
            hold_times.append((closed - opened).total_seconds() / 60)
        except Exception:
            pass
    avg_hold_min = sum(hold_times) / len(hold_times) if hold_times else 0.0
    by_label = {}
    for lbl in ("SCALPER", "MOONSHOT", "REVERSAL", "TRINITY", "PRE_BREAKOUT"):
        lt = [t for t in full if t.get("label") == lbl]
        if not lt:
            continue
        lw = [t for t in lt if t["pnl_pct"] > 0]
        ll = [t for t in lt if t["pnl_pct"] <= 0]
        by_label[lbl] = {
            "total":    len(lt),
            "wins":     len(lw),
            "win_rate": len(lw) / len(lt) * 100,
            "avg_win":  sum(t["pnl_pct"] for t in lw) / len(lw) if lw else 0.0,
            "avg_loss": sum(t["pnl_pct"] for t in ll) / len(ll) if ll else 0.0,
            "total_pnl":sum(t["pnl_usdt"] for t in lt),
        }
    # Exit reason breakdown with P&L (not just counts)
    by_reason: dict = {}
    for t in full:
        r = t.get("exit_reason", "UNKNOWN")
        if r not in by_reason:
            by_reason[r] = {"count": 0, "pnl_sum": 0.0, "wins": 0}
        by_reason[r]["count"] += 1
        by_reason[r]["pnl_sum"] += t.get("pnl_usdt", 0)
        if t.get("pnl_pct", 0) > 0:
            by_reason[r]["wins"] += 1
    givebacks = [t.get("giveback_ratio", 0) for t in full
                 if t.get("giveback_ratio") is not None and t.get("peak_profit_pct", 0) > 0.5]
    avg_giveback = sum(givebacks) / len(givebacks) if givebacks else None
    maturities = [t.get("move_maturity", 0) for t in full
                  if t.get("move_maturity") is not None]
    avg_maturity = sum(maturities) / len(maturities) if maturities else None
    by_signal = _compute_signal_stats(full)
    return {
        "total":         n,
        "wins":          len(wins),
        "losses":        len(losses),
        "win_rate":      len(wins) / n * 100,
        "avg_win":       sum(wins)  / len(wins)  if wins   else 0.0,
        "avg_loss":      sum(losses)/ len(losses) if losses else 0.0,
        "avg_win_usdt":  sum(wins_usdt) / len(wins_usdt) if wins_usdt else 0.0,
        "avg_loss_usdt": sum(losses_usdt) / len(losses_usdt) if losses_usdt else 0.0,
        "profit_factor": profit_factor,
        "total_pnl":     sum(pnls_usdt),
        "max_drawdown":  max_dd,
        "sharpe":        sharpe,
        "expectancy":    expectancy,
        "avg_hold_min":  avg_hold_min,
        "best":          best,
        "worst":         worst,
        "by_label":      by_label,
        "by_reason":     by_reason,
        "by_signal":     by_signal,
        "avg_giveback":  avg_giveback,
        "avg_maturity":  avg_maturity,
        "since_label":   since_label,
    }

def _cmd_pnl(balance: float):
    """Show P&L snapshot: today + session, using trade_history."""
    mode  = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    today_trades = [t for t in trade_history
                    if t.get("closed_at", "")[:10] == today
                    and not t.get("is_partial")]
    all_full = [t for t in trade_history if not t.get("is_partial")]
    all_pnl  = sum(t["pnl_usdt"] for t in trade_history)  # includes partials

    def _block(trades: list, label: str) -> str:
        if not trades:
            return ""
        wins = [t for t in trades if t["pnl_pct"] > 0]
        pnl  = sum(t["pnl_usdt"] for t in trades)
        wr   = len(wins) / len(trades) * 100
        emoji = "📈" if pnl >= 0 else "📉"
        return (f"\n{emoji} <b>{label}</b>: {len(trades)}t  "
                f"{wr:.0f}%WR  <b>${pnl:+.2f}</b>")

    def _strategy_line(trades: list) -> str:
        lines = []
        icons = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄", "TRINITY": "🔱", "PRE_BREAKOUT": "🔮"}
        for lbl in ("SCALPER", "MOONSHOT", "REVERSAL", "TRINITY", "PRE_BREAKOUT"):
            lt = [t for t in trades if t.get("label") == lbl]
            if not lt:
                continue
            wins = [t for t in lt if t["pnl_pct"] > 0]
            pnl  = sum(t["pnl_usdt"] for t in lt)
            icon = icons.get(lbl, "•")
            lines.append(f"  {icon} {lbl}: {len(lt)}t {len(wins)}W ${pnl:+.2f}")
        return "\n".join(lines) if lines else "  No trades"

    # Today section
    if today_trades:
        today_pnl = sum(t["pnl_usdt"] for t in today_trades)
        today_wins = sum(1 for t in today_trades if t["pnl_pct"] > 0)
        today_emoji = "📈" if today_pnl >= 0 else "📉"
        best_today  = max(today_trades, key=lambda t: t["pnl_usdt"])
        worst_today = min(today_trades, key=lambda t: t["pnl_usdt"])
        today_section = (
            f"{today_emoji} <b>Today</b> ({today})\n"
            f"  {len(today_trades)} trades | {today_wins}W {len(today_trades)-today_wins}L | "
            f"<b>${today_pnl:+.2f}</b>\n"
            f"{_strategy_line(today_trades)}\n"
            f"  Best:  {best_today['symbol']} ${best_today['pnl_usdt']:+.2f}\n"
            f"  Worst: {worst_today['symbol']} ${worst_today['pnl_usdt']:+.2f}"
        )
    else:
        today_section = f"📊 <b>Today</b> ({today})\n  No closed trades yet"

    # Session section
    session_wins = sum(1 for t in all_full if t["pnl_pct"] > 0)
    session_emoji = "📈" if all_pnl >= 0 else "📉"
    session_section = (
        f"\n━━━━━━━━━━━━━━━\n"
        f"{session_emoji} <b>Session</b> ({len(all_full)} trades)\n"
        f"  {session_wins}W {len(all_full)-session_wins}L | <b>${all_pnl:+.2f}</b>\n"
        f"{_strategy_line(all_full)}"
    )

    # Open positions
    open_pnl = 0.0
    open_lines = []
    for t in scalper_trades + alt_trades:
        px, pct = _trade_price_pct(t)
        if px and pct is not None:
            unrealized = (px - t["entry_price"]) * t["qty"]
            open_pnl += unrealized
            open_lines.append(f"  {t['label']}: {t['symbol']} {pct:+.1f}% (${unrealized:+.2f})")
    open_section = ""
    if open_lines:
        open_section = (
            f"\n━━━━━━━━━━━━━━━\n"
            f"📌 <b>Open</b> (unrealized: <b>${open_pnl:+.2f}</b>)\n"
            + "\n".join(open_lines)
        )

    telegram(
        f"💰 <b>P&L Report</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{today_section}"
        f"{session_section}"
        f"{open_section}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${balance:.2f}</b>"
    )

def _cmd_metrics(balance: float):
    full = [t for t in trade_history if not t.get("is_partial")]
    if not full:
        telegram("📊 <b>Metrics</b>\n━━━━━━━━━━━━━━━\nNo completed trades yet.")
        return
    m = _compute_metrics(trade_history)
    pf_str = f"{m['profit_factor']:.2f}" if not math.isinf(m["profit_factor"]) else "∞"
    hold_str = (f"{m['avg_hold_min']:.0f}min" if m["avg_hold_min"] < 120
                else f"{m['avg_hold_min']/60:.1f}h")
    lines  = [
        f"📊 <b>Performance Metrics</b>",
        f"━━━━━━━━━━━━━━━",
        f"Trades:      <b>{m['total']}</b>  ({m['wins']}W / {m['losses']}L)",
        f"Win rate:    <b>{m['win_rate']:.1f}%</b>  |  Avg hold: {hold_str}",
        f"Avg win:     <b>+{m['avg_win']:.2f}%</b> (${m['avg_win_usdt']:+.2f})",
        f"Avg loss:    <b>{m['avg_loss']:.2f}%</b> (${m['avg_loss_usdt']:+.2f})",
        f"Expectancy:  <b>${m['expectancy']:+.2f}</b>/trade",
        f"P-factor:    <b>{pf_str}</b>  |  Sharpe: <b>{m['sharpe']:.2f}</b>",
        f"Total P&L:   <b>${m['total_pnl']:+.2f}</b>  |  Max DD: <b>-${m['max_drawdown']:.2f}</b>",
        f"Balance:     <b>${balance:.2f}</b>",
    ]
    icons = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄", "TRINITY": "🔱", "PRE_BREAKOUT": "🔮"}
    if m["by_label"]:
        lines.append("━━━━━━━━━━━━━━━")
        for lbl, s in m["by_label"].items():
            icon = icons.get(lbl, "•")
            lines.append(
                f"{icon} <b>{lbl}</b>  {s['total']}t  "
                f"{s['win_rate']:.0f}%WR  "
                f"${s['total_pnl']:+.2f}  "
                f"avg +{s['avg_win']:.1f}%/{s['avg_loss']:.1f}%"
            )
    # Exit reasons with P&L (not just counts)
    if m["by_reason"]:
        lines.append("━━━━━━━━━━━━━━━")
        lines.append("Exit reasons:")
        for r, data in sorted(m["by_reason"].items(), key=lambda x: -x[1]["count"]):
            avg_pnl = data["pnl_sum"] / data["count"] if data["count"] > 0 else 0
            wr = data["wins"] / data["count"] * 100 if data["count"] > 0 else 0
            emoji = "✅" if avg_pnl > 0 else "⚠️" if wr >= 40 else "🔴"
            lines.append(f"  {emoji} {r}: {data['count']}t "
                         f"{wr:.0f}%WR ${data['pnl_sum']:+.2f} "
                         f"(avg ${avg_pnl:+.2f})")
    if m.get("by_signal"):
        sig_parts = []
        for sig, s in sorted(m["by_signal"].items(),
                              key=lambda x: -x[1]["total"]):
            if s["total"] < 2:
                continue
            emoji = "✅" if s["win_rate"] >= 50 else "⚠️" if s["win_rate"] >= 30 else "🔴"
            sig_parts.append(f"  {emoji} {sig}: {s['total']}t "
                             f"{s['win_rate']:.0f}%WR "
                             f"avg {s['avg_pnl']:+.1f}%")
        if sig_parts:
            lines.append("━━━━━━━━━━━━━━━")
            lines.append("Entry signals:")
            lines.extend(sig_parts)
    best  = m["best"]
    worst = m["worst"]
    lines.append("━━━━━━━━━━━━━━━")
    lines.append(f"Best:  {best['symbol']} {best['pnl_pct']:+.2f}% ${best.get('pnl_usdt',0):+.2f} "
                 f"({best.get('exit_reason','?')})")
    lines.append(f"Worst: {worst['symbol']} {worst['pnl_pct']:+.2f}% ${worst.get('pnl_usdt',0):+.2f} "
                 f"({worst.get('exit_reason','?')})")
    adaptive_lines = []
    if m.get("avg_giveback") is not None:
        gb = m["avg_giveback"]
        gb_status = ("✅ optimal" if GIVEBACK_TARGET_LOW <= gb <= GIVEBACK_TARGET_HIGH
                     else "⚠️ trail too wide" if gb > GIVEBACK_TARGET_HIGH
                     else "⚠️ trail too tight")
        adaptive_lines.append(f"Giveback: {gb*100:.0f}% ({gb_status})")
    if m.get("avg_maturity") is not None:
        mat = m["avg_maturity"]
        mat_status = ("✅ early" if mat < 0.6
                      else "⚠️ mid-move" if mat < 0.8
                      else "🔴 late")
        adaptive_lines.append(f"Maturity: {mat*100:.0f}% ({mat_status})")
    s_off = _adaptive_offsets.get("SCALPER", 0)
    m_off = _adaptive_offsets.get("MOONSHOT", 0)
    if s_off != 0 or m_off != 0:
        adaptive_lines.append(f"Thresholds: S={get_effective_threshold('SCALPER'):.0f} "
                              f"M={get_effective_threshold('MOONSHOT'):.0f}")
    if adaptive_lines:
        lines.append("━━━━━━━━━━━━━━━")
        lines.append("🧬 " + " | ".join(adaptive_lines))
    telegram("\n".join(lines)[:4000])

def _cmd_config():
    now_ts      = time.time()
    dead_active = sum(1 for v in _liquidity_blacklist.values() if v > now_ts)
    # Market regime
    mult = _market_regime_mult
    if mult > 1.30: rl = "🔴 CRASH"
    elif mult > 1.10: rl = "🟠 BEAR"
    elif mult > 0.95: rl = "⚪ SIDEWAYS"
    elif mult > 0.80: rl = "🟢 BULL"
    else: rl = "🚀 STRONG BULL"
    mg = "✅" if _moonshot_gate_open else "⛔"
    telegram(
        f"⚙️ <b>Config</b>\n━━━━━━━━━━━━━━━\n"
        f"<b>Market</b>: {rl} (×{mult:.2f}) | BTC {_btc_ema_gap_macro*100:+.1f}%\n"
        f"Moon gate: {mg} ({MOONSHOT_BTC_EMA_GATE*100:.0f}%/{MOONSHOT_BTC_GATE_REOPEN*100:.0f}%)\n"
        f"━━━━━━━━━━━━━━━\n"
        f"💰 S {SCALPER_ALLOCATION_PCT*100:.0f}% | M {MOONSHOT_ALLOCATION_PCT*100:.0f}% | T {TRINITY_ALLOCATION_PCT*100:.0f}%\n"
        f"🟢 <b>Scalper</b> ×{SCALPER_MAX_TRADES}\n"
        f"  TP {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% | SL {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}%\n"
        f"  Trail {SCALPER_PROG_CEILING*100:.1f}→{SCALPER_PROG_FLOOR*100:.1f}% | "
        f"BE ≥{SCALPER_BREAKEVEN_SCORE}pts +{SCALPER_BREAKEVEN_ACT*100:.1f}%\n"
        f"  WL: {len(_watchlist)} pairs | Thresh: {get_effective_threshold('SCALPER'):.0f}\n"
        f"🌙 <b>Moon</b> ×{ALT_MAX_TRADES}\n"
        f"  TP +{MOONSHOT_TP_INITIAL*100:.0f}% | SL ATR×{MOONSHOT_SL_ATR_MULT:.1f}\n"
        f"  μTP +{MOONSHOT_MICRO_TP_PCT*100:.0f}% → ½TP +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}% → F&C\n"
        f"  Trail {PROG_TRAIL_CEILING*100:.0f}→{PROG_TRAIL_FLOOR*100:.1f}% | "
        f"TO {MOONSHOT_TIMEOUT_FLAT_MINS}/{MOONSHOT_TIMEOUT_MARGINAL_MINS}/{MOONSHOT_TIMEOUT_MAX_MINS}min\n"
        f"🔱 <b>Trinity</b> ×{TRINITY_MAX_CONCURRENT} | {TRINITY_INTERVAL}\n"
        f"  {'/'.join(s[:3] for s in TRINITY_SYMBOLS)} | drop ≥{TRINITY_DROP_PCT*100:.0f}% | "
        f"RSI {TRINITY_MIN_RSI:.0f}–{TRINITY_MAX_RSI:.0f} | {TRINITY_MAX_HOURS}h\n"
        f"🔄 <b>Reversal</b> | TP +{REVERSAL_TP*100:.1f}% | {REVERSAL_MAX_HOURS}h\n"
        f"🔮 <b>Pre-break</b> | TP +{PRE_BREAKOUT_TP*100:.0f}% | {PRE_BREAKOUT_MAX_HOURS}h\n"
        f"━━━━━━━━━━━━━━━\n"
        f"🛡️ CB: {MAX_CONSECUTIVE_LOSSES}L streak | Session -{SESSION_LOSS_PAUSE_PCT*100:.0f}% | "
        f"WR <{WIN_RATE_CB_THRESHOLD*100:.0f}%\n"
        f"🧬 S={get_effective_threshold('SCALPER'):.0f} M={get_effective_threshold('MOONSHOT'):.0f} | "
        f"☠️ {dead_active} blacklisted\n"
        f"{'⏸️ PAUSED' if _paused else '▶️ RUNNING'}"
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

def _cmd_restart():
    telegram("🔄 <b>Restarting...</b> State saved.")
    save_state()
    os._exit(1)  # non-zero exit code triggers Railway auto-restart

def _cmd_resetstreak():
    global _consecutive_losses, _win_rate_pause_until, _streak_paused_at
    _consecutive_losses    = 0
    _win_rate_pause_until  = 0.0
    _streak_paused_at      = 0.0
    save_state()
    telegram("✅ <b>Streak reset.</b> Losses cleared, entries resumed.")

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
                f"signal={t.get('entry_signal','?')} "
                f"pnl={t.get('pnl_pct',0):+.2f}% reason={t.get('exit_reason','?')} "
                f"score={t.get('score',0):.0f} rsi={t.get('rsi',0):.0f} held={held}min"
            )
    open_ctx = []
    for t in scalper_trades + alt_trades:
        try:
            px  = ws_price(t["symbol"]) or float(public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"])
            pct = (px - t["entry_price"]) / t["entry_price"] * 100
            open_ctx.append(f"{t['symbol']} [{t['label']}] currently {pct:+.2f}%")
        except Exception:
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
        data = _get_session().get(
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
            if   text == "/pnl":    _cmd_pnl(balance)
            elif text == "/status":  _cmd_status(balance)
            elif text == "/metrics": _cmd_metrics(balance)
            elif text == "/logs":
                out = ("📜 <b>Last Scanner Activity</b>\n━━━━━━━━━━━━━━━\n"
                       + "\n".join(f"<code>{l}</code>" for l in _scanner_log_buffer)
                       if _scanner_log_buffer else "📜 No scanner activity yet.")
                telegram(out)
            elif text == "/pause":
                _paused = True
                save_state()
                telegram("⏸️ <b>Paused.</b> Open positions monitored. /resume to restart.")
            elif text == "/resume":
                _paused = False
                save_state()
                telegram("▶️ <b>Resumed.</b> Scanning for new trades.")
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

def reconcile_open_positions():
    if PAPER_TRADE:
        if scalper_trades or alt_trades:
            log.info(f"✅ [PAPER] Restored {len(scalper_trades)} scalper + {len(alt_trades)} alt trades.")
        return
    try:
        # IMPORTANT: Use free+locked to avoid thinking positions are closed when they have open limit orders
        balances = {b["asset"]: float(b.get("free", 0)) + float(b.get("locked", 0))
                    for b in private_get("/api/v3/account").get("balances", [])}
        if scalper_trades or alt_trades:
            stale = []
            for trade in list(scalper_trades + alt_trades):
                asset = trade["symbol"].replace("USDT", "")
                held  = balances.get(asset, 0.0)
                expected_qty = trade.get("qty", 0)
                if expected_qty > 0 and held < expected_qty * 0.05:
                    stale.append(trade)
                    log.warning(f"⚠️  [{trade['label']}] {trade['symbol']}: state says "
                                f"qty={expected_qty:.4f} but exchange shows {held:.4f} — "
                                f"position likely closed while bot was down")
            if stale:
                for trade in stale:
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
                    f"⚠️ <b>Positions closed offline</b>\n"
                    f"{', '.join(syms)} — check MEXC for P&L"
                )
            elif scalper_trades or alt_trades:
                log.info(f"✅ Restored {len(scalper_trades)} scalper + {len(alt_trades)} alt trades "
                         f"— exchange balances confirmed.")
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
                    telegram(f"⚠️ <b>Untracked holdings</b>\n" + "\n".join(untracked))
        open_orders = private_get("/api/v3/openOrders", {})
        if not open_orders:
            return
        known_symbols = {t["symbol"] for t in scalper_trades + alt_trades}
        orphan_orders = [o for o in open_orders if o["symbol"] not in known_symbols]
        if orphan_orders:
            syms = list({o["symbol"] for o in orphan_orders})
            log.warning(f"⚠️  Found {len(orphan_orders)} orphaned order(s) with no state: {syms}")
            telegram(f"⚠️ <b>Orphaned orders</b> | {', '.join(syms)} — check MEXC")
    except Exception as e:
        log.error(f"Reconcile failed: {e}")

# Helper to get strategy capital
def get_strategy_capital(balance: float, strategy: str) -> float:
    if strategy == "SCALPER":
        return balance * SCALPER_ALLOCATION_PCT
    elif strategy == "MOONSHOT":
        return balance * MOONSHOT_ALLOCATION_PCT
    elif strategy == "TRINITY":
        return balance * TRINITY_ALLOCATION_PCT
    else:
        return balance

def compute_market_regime_multiplier(df_btc: pd.DataFrame) -> float:
    """
    Compute a multiplier for entry thresholds based on BTC volatility and trend.
    Returns multiplier (e.g., 0.8 = tighten, 1.2 = loosen).
    """
    try:
        # Volatility: ATR ratio (last ATR / average ATR over 40 candles)
        tr = pd.concat([
            df_btc["high"] - df_btc["low"],
            (df_btc["high"] - df_btc["close"].shift(1)).abs(),
            (df_btc["low"]  - df_btc["close"].shift(1)).abs(),
        ], axis=1).max(axis=1)
        atr = tr.ewm(alpha=1.0 / 14, adjust=False).mean()
        if len(atr) > 40:
            atr_ratio = atr.iloc[-1] / atr.iloc[-41:-1].mean()
        else:
            atr_ratio = 1.0
        # Trend: EMA gap
        btc_ema = calc_ema(df_btc["close"], BTC_REGIME_EMA_PERIOD)
        ema_gap = (float(df_btc["close"].iloc[-1]) / float(btc_ema.iloc[-1]) - 1)

        multiplier = 1.0
        # Volatility adjustments
        if atr_ratio > REGIME_HIGH_VOL_ATR_RATIO:
            multiplier *= REGIME_TIGHTEN_MULT
            log.debug(f"Market regime: high volatility (ATR ratio {atr_ratio:.2f}) → tighten ×{REGIME_TIGHTEN_MULT}")
        elif atr_ratio < REGIME_LOW_VOL_ATR_RATIO:
            multiplier *= REGIME_LOOSEN_MULT
            log.debug(f"Market regime: low volatility (ATR ratio {atr_ratio:.2f}) → loosen ×{REGIME_LOOSEN_MULT}")

        # Trend adjustments
        if ema_gap > REGIME_STRONG_UPTREND_GAP:
            multiplier *= REGIME_TREND_MULT
            log.debug(f"Market regime: strong uptrend (EMA gap {ema_gap*100:.1f}%) → loosen ×{REGIME_TREND_MULT}")
        elif ema_gap < REGIME_STRONG_DOWNTREND_GAP:
            multiplier *= REGIME_TIGHTEN_MULT
            log.debug(f"Market regime: strong downtrend (EMA gap {ema_gap*100:.1f}%) → tighten ×{REGIME_TIGHTEN_MULT}")

        return max(0.7, min(1.6, multiplier))  # clamp to 0.7–1.6
    except Exception as e:
        log.debug(f"Market regime computation failed: {e}")
        return 1.0

def flush_telegram_updates():
    """Consume all pending Telegram updates without processing them.
    Prevents stale commands (like /restart) from re-triggering on boot."""
    global last_telegram_update
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        data = _get_session().get(
            f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates",
            params={"timeout": 0, "limit": 100},
            timeout=5,
        ).json()
        updates = data.get("result", [])
        if updates:
            last_telegram_update = updates[-1]["update_id"]
            log.info(f"🔌 Flushed {len(updates)} stale Telegram update(s)")
    except Exception as e:
        log.debug(f"Telegram flush failed: {e}")

def startup() -> float:
    global scalper_trades, alt_trades, trade_history, _consecutive_losses, \
           _win_rate_pause_until, _streak_paused_at, _paused, \
           _scalper_excluded, _alt_excluded, _api_blacklist, \
           _liquidity_blacklist, _liquidity_fail_count, \
           _adaptive_offsets, _last_rebalance_count, \
           _dynamic_scalper_budget, _dynamic_moonshot_budget
    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")
    flush_telegram_updates()  # clear stale commands (e.g. /restart) before processing
    _load_symbol_rules()
    (scalper_trades, alt_trades, trade_history,
     _consecutive_losses, _win_rate_pause_until, _streak_paused_at,
     _paused, _scalper_excluded, _alt_excluded, _api_blacklist,
     _liquidity_blacklist, _liquidity_fail_count,
     _adaptive_offsets, _last_rebalance_count,
     _dynamic_scalper_budget, _dynamic_moonshot_budget) = load_state()
    if _adaptive_offsets.get("SCALPER", 0) != 0 or _adaptive_offsets.get("MOONSHOT", 0) != 0:
        log.info(f"🧠 [ADAPTIVE] Restored offsets: "
                 f"SCALPER {_adaptive_offsets.get('SCALPER',0):+.0f} "
                 f"MOONSHOT {_adaptive_offsets.get('MOONSHOT',0):+.0f}")
    if _dynamic_scalper_budget or _dynamic_moonshot_budget:
        log.info(f"💼 [REBALANCE] Restored budgets: "
                 f"Scalper {(_dynamic_scalper_budget or SCALPER_BUDGET_PCT)*100:.0f}% "
                 f"Moonshot {(_dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT)*100:.0f}%")
    if _paused:
        log.info("⏸️  Bot restored in PAUSED state — send /resume to restart scanning")
    reconcile_open_positions()
    _start_ws_monitor()
    log.info("📋 Building initial watchlist...")
    build_watchlist(fetch_tickers())
    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"💰 <b>${startup_balance:.2f}</b> | "
        f"S {SCALPER_ALLOCATION_PCT*100:.0f}% M {MOONSHOT_ALLOCATION_PCT*100:.0f}% T {TRINITY_ALLOCATION_PCT*100:.0f}%\n"
        f"━━━━━━━━━━━━━━━\n"
        f"🟢 Scalper × {SCALPER_MAX_TRADES} | TP {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% | "
        f"SL {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}% | trail prog\n"
        f"🌙 Moon × {ALT_MAX_TRADES} | TP +{MOONSHOT_TP_INITIAL*100:.0f}% | "
        f"μTP +{MOONSHOT_MICRO_TP_PCT*100:.0f}% ½TP +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}% → F&C\n"
        f"🔱 Trinity × {TRINITY_MAX_CONCURRENT} | {TRINITY_INTERVAL} | "
        f"drop ≥{TRINITY_DROP_PCT*100:.0f}% | {TRINITY_MAX_HOURS}h\n"
        f"🔄 Reversal | TP +{REVERSAL_TP*100:.1f}% | "
        f"SL cap-anchored | {REVERSAL_MAX_HOURS}h\n"
        f"🔮 Pre-breakout | TP +{PRE_BREAKOUT_TP*100:.0f}% | {PRE_BREAKOUT_MAX_HOURS}h\n"
        f"━━━━━━━━━━━━━━━\n"
        f"🛡️ BTC gate {MOONSHOT_BTC_EMA_GATE*100:.0f}%/{MOONSHOT_BTC_GATE_REOPEN*100:.0f}% | "
        f"CB {MAX_CONSECUTIVE_LOSSES}L | Session -{SESSION_LOSS_PAUSE_PCT*100:.0f}%\n"
        f"{'🧠 AI ✅' if SENTIMENT_ENABLED else '🧠 AI ⚠️'} | "
        f"📊 Adaptive ✅ | ⏸️ {'PAUSED' if _paused else 'Active'}\n"
        f"<i>/status /pnl /metrics /config /pause /close /restart /ask</i>"
    )
    return startup_balance

def run():
    global _last_rotation_scan, _watchlist, _watchlist_at, \
           _last_rebound_rebuild, \
           _scalper_excluded, _alt_excluded, _btc_ema_gap, _btc_ema_gap_macro, \
           _streak_paused_at, _consecutive_losses, _win_rate_pause_until, \
           _paused, _fast_cycle_counter, _market_regime_mult, \
           _moonshot_gate_open, _session_loss_paused_until, \
           _strategy_loss_streaks, _strategy_paused_until
    startup_balance  = startup()
    balance          = get_available_balance()
    # Initialize BTC macro EMA gap BEFORE first entry cycle (prevents gate race condition)
    try:
        df_btc_init = parse_klines("BTCUSDT", interval="1h", limit=120, min_len=50)
        if df_btc_init is not None:
            btc_ema_init = calc_ema(df_btc_init["close"], BTC_REGIME_EMA_PERIOD)
            _btc_ema_gap_macro = (float(df_btc_init["close"].iloc[-1]) / float(btc_ema_init.iloc[-1]) - 1)
            _market_regime_mult = compute_market_regime_multiplier(df_btc_init)
            if _btc_ema_gap_macro < MOONSHOT_BTC_EMA_GATE:
                _moonshot_gate_open = False
            log.info(f"📊 BTC 1h EMA gap: {_btc_ema_gap_macro*100:+.1f}% | "
                     f"Regime: {_market_regime_mult:.2f}× | "
                     f"Moon gate: {'✅' if _moonshot_gate_open else '⛔'}")
    except Exception as e:
        log.warning(f"BTC 1h init failed: {e} — gate defaults to open")
    while True:
        try:
            listen_for_commands(balance)
            balance = get_available_balance()
            # Compute allocated capitals
            scalper_capital   = get_strategy_capital(balance, "SCALPER")
            moonshot_capital  = get_strategy_capital(balance, "MOONSHOT")
            trinity_capital   = get_strategy_capital(balance, "TRINITY")

            _load_symbol_rules()
            all_trades   = scalper_trades + alt_trades
            open_symbols = {t["symbol"] for t in all_trades}
            total_value = balance
            for t in all_trades:
                if not PAPER_TRADE:
                    try:
                        px = ws_price(t["symbol"]) or float(
                            public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"]
                        )
                        total_value += px * t["qty"]
                    except Exception:
                        total_value += t["budget_used"]
                else:
                    total_value += t["budget_used"]
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
                    f"🛑 <b>Daily loss limit</b> | P&L ${daily_pnl:.2f}\n"
                    f"Scalper entries paused until midnight UTC."
                )
            elif not daily_cb:
                run._circuit_alerted_today = ""
            if streak_cb and not getattr(run, "_streak_alerted", False):
                run._streak_alerted = True
                _streak_paused_at   = time.time()
                telegram(
                    f"🛑 <b>Loss streak</b> | {_consecutive_losses} consecutive losses\n"
                    f"Scalper entries paused. /resetstreak to override."
                )
            elif not streak_cb:
                run._streak_alerted = False
            if (streak_cb
                    and not scalper_trades
                    and _streak_paused_at > 0
                    and time.time() - _streak_paused_at >= STREAK_AUTO_RESET_MINS * 60):
                _consecutive_losses = 0
                _streak_paused_at   = 0.0
                run._streak_alerted = False
                save_state()
                log.info(f"✅ Streak CB auto-reset after {STREAK_AUTO_RESET_MINS}min with no open positions")
                telegram(f"✅ <b>Streak auto-reset</b> | {STREAK_AUTO_RESET_MINS}min idle | entries resumed")
                streak_cb    = False
                circuit_open = daily_cb or win_rate_cb
            open_exposure = sum(t.get("budget_used", 0) for t in all_trades)
            over_exposed  = (open_exposure / balance > MAX_EXPOSURE_PCT) if balance > 0 else False
            if over_exposed:
                log.debug(f"⚠️ Over-exposed (${open_exposure:.0f} / ${balance:.0f}) — skipping new entries")

            # P2: Session P&L pause — stop ALL entries if bleeding too much
            session_pnl = sum(t.get("pnl_usdt", 0) for t in trade_history)
            session_loss_limit = -(balance * SESSION_LOSS_PAUSE_PCT)
            session_paused = False
            if _session_loss_paused_until > time.time():
                session_paused = True
                if int(time.time()) % 300 < 3:
                    mins_left = (_session_loss_paused_until - time.time()) / 60
                    log.info(f"🛑 Session P&L pause active ({mins_left:.0f}min remaining, P&L ${session_pnl:.2f})")
            elif session_pnl < session_loss_limit and len(trade_history) >= 3:
                _session_loss_paused_until = time.time() + SESSION_LOSS_PAUSE_MINS * 60
                session_paused = True
                telegram(f"🛑 <b>Session loss limit</b> | P&L ${session_pnl:.2f}\n"
                         f"All entries paused {SESSION_LOSS_PAUSE_MINS}min.")

            # P5: Regime-adaptive alt slots (more trades in bull, fewer in bear)
            effective_alt_max = ALT_MAX_TRADES
            if _market_regime_mult < 0.90:
                effective_alt_max = ALT_MAX_TRADES + 1  # bull: 3 slots
            elif _market_regime_mult > 1.20:
                effective_alt_max = max(1, ALT_MAX_TRADES - 1)  # bear: 1 slot

            scalper_needs_entry = (not _paused and not session_paused and not circuit_open
                                   and not over_exposed
                                   and len(scalper_trades) < SCALPER_MAX_TRADES)
            alt_needs_entry     = (not _paused and not session_paused and not over_exposed
                                   and (sum(1 for t in alt_trades if t["label"] != "TRINITY") < effective_alt_max
                                        or sum(1 for t in alt_trades if t["label"] == "TRINITY") < TRINITY_MAX_CONCURRENT))
            btc_panic = False
            df_btc    = None
            df_btc_1h = None
            if scalper_needs_entry or alt_needs_entry:
                try:
                    df_btc = parse_klines("BTCUSDT", interval="5m", limit=120, min_len=105)
                    if df_btc is not None:
                        # Short-term EMA gap (5m, ~8h) for scalper penalty
                        btc_ema = calc_ema(df_btc["close"], BTC_REGIME_EMA_PERIOD)
                        _btc_ema_gap = (float(df_btc["close"].iloc[-1]) / float(btc_ema.iloc[-1]) - 1)
                        chg = (float(df_btc["close"].iloc[-1]) /
                               float(df_btc["open"].iloc[-1]) - 1)
                        if chg < -BTC_PANIC_DROP:
                            btc_panic = True
                            log.warning(f"🚨 BTC panic: {chg*100:.2f}% — ALL entries paused this cycle")
                except Exception:
                    pass
                # Macro BTC health (1h candles, 100-period EMA = ~4 days) for moonshot gate
                try:
                    df_btc_1h = parse_klines("BTCUSDT", interval="1h", limit=120, min_len=50)
                    if df_btc_1h is not None:
                        btc_ema_1h = calc_ema(df_btc_1h["close"], BTC_REGIME_EMA_PERIOD)
                        _btc_ema_gap_macro = (float(df_btc_1h["close"].iloc[-1]) / float(btc_ema_1h.iloc[-1]) - 1)
                    else:
                        _btc_ema_gap_macro = _btc_ema_gap  # fallback to 5m
                except Exception:
                    _btc_ema_gap_macro = _btc_ema_gap  # fallback to 5m
            # volatility regime guard (pause scalper entries)
            if scalper_needs_entry and df_btc is not None:
                try:
                    tr = pd.concat([
                        df_btc["high"] - df_btc["low"],
                        (df_btc["high"] - df_btc["close"].shift(1)).abs(),
                        (df_btc["low"]  - df_btc["close"].shift(1)).abs(),
                    ], axis=1).max(axis=1)
                    atr = tr.ewm(alpha=1.0 / 14, adjust=False).mean()
                    atr_ratio = atr.iloc[-1] / atr.iloc[-41:-1].mean() if len(atr) > 40 else 1.0
                    if atr_ratio > 1.85:
                        scalper_needs_entry = False
                        log.warning(f"🌪️ BTC extreme volatility regime (ATR ratio {atr_ratio:.2f}) — scalper entries PAUSED")
                except Exception as e:
                    log.debug(f"Volatility guard error: {e}")
            # Compute market regime multiplier (prefer 1h macro data)
            if df_btc_1h is not None:
                _market_regime_mult = compute_market_regime_multiplier(df_btc_1h)
            elif df_btc is not None:
                _market_regime_mult = compute_market_regime_multiplier(df_btc)
            else:
                _market_regime_mult = 1.0
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
            if time.time() - _watchlist_at >= WATCHLIST_TTL:
                log.info("📋 Watchlist TTL expired — rebuilding...")
                build_watchlist(tickers if tickers is not None else fetch_tickers())
            if (df_btc is not None
                    and not btc_panic
                    and time.time() - _last_rebound_rebuild >= WATCHLIST_REBOUND_MIN_INTERVAL
                    and time.time() - _watchlist_at >= WATCHLIST_REBOUND_MIN_INTERVAL):
                try:
                    btc_close = df_btc["close"]
                    btc_open  = df_btc["open"]
                    last_chg  = float(btc_close.iloc[-1]) / float(btc_open.iloc[-1]) - 1
                    prev_chg  = float(btc_close.iloc[-2]) / float(btc_open.iloc[-2]) - 1
                    if last_chg >= BTC_REBOUND_PCT and prev_chg >= BTC_REBOUND_CONFIRM_PCTS:
                        _last_rebound_rebuild = time.time()
                        log.info(
                            f"📈 BTC rebound confirmed "
                            f"(last={last_chg*100:+.2f}% prev={prev_chg*100:+.2f}%) "
                            f"— forcing early watchlist rebuild"
                        )
                        build_watchlist(tickers if tickers is not None else fetch_tickers())
                except Exception as _e:
                    log.debug(f"BTC rebound check error: {_e}")
            # Scalper entry
            if scalper_needs_entry:
                used_scalper = sum(t["budget_used"] for t in scalper_trades)
                available_scalper = scalper_capital - used_scalper
                if available_scalper <= 0:
                    log.info(f"💰 Scalper capital depleted (${available_scalper:.2f}) — no new entries")
                else:
                    opp = find_scalper_opportunity(available_scalper,
                                                   exclude=_scalper_excluded,
                                                   open_symbols=open_symbols)
                    if opp and (_btc_ema_gap < 0 or _btc_ema_gap_macro < 0):
                        # Use the worse (more negative) of 5m and 1h EMA gaps
                        worst_gap = min(_btc_ema_gap, _btc_ema_gap_macro)
                        penalty = round(abs(worst_gap) * BTC_REGIME_EMA_PENALTY, 1)
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
                        trade_budget, pre_tp, pre_sl, _, _ = calc_risk_budget(opp, scalper_capital)
                        trade_budget = min(trade_budget, available_scalper)
                        if trade_budget <= 0:
                            log.info(f"💰 [SCALPER] Budget zero after cap — skipping")
                        else:
                            gap = opp.get("score", SCALPER_THRESHOLD) - SCALPER_THRESHOLD
                            opp["kelly_mult"] = (KELLY_MULT_HIGH_CONF if gap >= 45
                                                 else KELLY_MULT_STANDARD if gap >= 30
                                                 else KELLY_MULT_SOLID    if gap >= 15
                                                 else KELLY_MULT_MARGINAL)
                            log.info(f"💰 [SCALPER] Risk budget: ${trade_budget:.2f} "
                                     f"(Kelly {opp['kelly_mult']:.2f}× | 1% risk @ SL {pre_sl*100:.2f}%, "
                                     f"cap ${available_scalper:.2f})")
                            trade = open_position(opp, trade_budget, pre_tp, pre_sl, "SCALPER")
                            if trade:
                                scalper_trades.append(trade)
                                _scalper_excluded.pop(opp["symbol"], None)
            # Scalper exits and rotation
            if scalper_trades:
                best_opp   = None
                best_score = 0
                at_max = len(scalper_trades) >= SCALPER_MAX_TRADES
                if at_max and not circuit_open:
                    now = time.time()
                    if now - _last_rotation_scan >= ROTATION_SCAN_INTERVAL:
                        _last_rotation_scan = now
                        used_scalper = sum(t["budget_used"] for t in scalper_trades)
                        available_scalper = scalper_capital - used_scalper
                        if available_scalper > 0:
                            best_opp = find_scalper_opportunity(available_scalper,
                                                                exclude=_scalper_excluded,
                                                                open_symbols=open_symbols)
                            best_score = best_opp["score"] if best_opp else 0
                worst_pct = min((t.get("highest_price", t["entry_price"]) /
                                 t["entry_price"] - 1) * 100 for t in scalper_trades)
                for trade in scalper_trades[:]:
                    tpct     = (trade.get("highest_price", trade["entry_price"]) /
                                trade["entry_price"] - 1) * 100
                    s_arg    = best_score if abs(tpct - worst_pct) < 0.01 else 0
                    should_exit, reason = check_exit(trade, best_score=s_arg)
                    if should_exit:
                        if reason == "PARTIAL_TP":
                            execute_partial_tp(trade)
                            # If FULL_CLOSE happened, remaining is 0 — remove trade
                            if trade["qty"] <= 0:
                                scalper_trades.remove(trade)
                        elif reason in ("STOP_LOSS", "TRAILING_STOP", "FLAT_EXIT", "TIMEOUT", "PROTECT_STOP"):
                            _scalper_excluded[trade["symbol"]] = (
                                time.time() + SCALPER_SYMBOL_COOLDOWN
                            )
                            log.info(f"⏳ [SCALPER] {trade['symbol']} in cooldown "
                                     f"for {SCALPER_SYMBOL_COOLDOWN//60}min after {reason}")
                            if close_position(trade, reason):
                                scalper_trades.remove(trade)
                        else:
                            if close_position(trade, reason):
                                scalper_trades.remove(trade)
                                if reason == "ROTATION" and best_opp:
                                    rot_eff_thresh = get_effective_threshold("SCALPER") * _market_regime_mult
                                    if best_opp["score"] >= rot_eff_thresh + SCALPER_ROTATE_GAP:
                                        rot_gap = best_opp.get("score", rot_eff_thresh) - rot_eff_thresh
                                        best_opp["kelly_mult"] = (
                                            KELLY_MULT_HIGH_CONF if rot_gap >= 45 else
                                            KELLY_MULT_STANDARD  if rot_gap >= 30 else
                                            KELLY_MULT_SOLID     if rot_gap >= 15 else
                                            KELLY_MULT_MARGINAL
                                        )
                                        rot_budget, rot_pre_tp, rot_pre_sl, _, _ = calc_risk_budget(best_opp, scalper_capital)
                                        used_scalper = sum(t["budget_used"] for t in scalper_trades)
                                        available_scalper = scalper_capital - used_scalper
                                        rot_budget = min(rot_budget, available_scalper)
                                        new_t = open_position(best_opp, rot_budget, rot_pre_tp, rot_pre_sl, "SCALPER")
                                        if new_t:
                                            scalper_trades.append(new_t)
                                            _scalper_excluded.pop(best_opp["symbol"], None)
                                    _scalper_excluded[trade["symbol"]] = time.time() + 900
            # Alt entries (moonshot, reversal, trinity)
            # Trinity gets PRIORITY entry — dip recovery on majors shouldn't wait for altcoin slots
            trinity_strategy_paused = _strategy_paused_until.get("TRINITY", 0) > time.time()
            if not _paused and not session_paused and not btc_panic and not over_exposed and not trinity_strategy_paused:
                used_trinity = sum(t["budget_used"] for t in alt_trades if t["label"] == "TRINITY")
                available_trinity = trinity_capital - used_trinity
                if available_trinity > 0:
                    opp = find_trinity_opportunity(total_value,
                                                   exclude=_alt_excluded,
                                                   open_symbols=open_symbols)
                    if opp:
                        trinity_budget = max(MOONSHOT_MIN_NOTIONAL, min(
                            round(trinity_capital * TRINITY_BUDGET_PCT, 2), available_trinity))
                        trade = open_position(opp, trinity_budget,
                                              opp["tp_pct"], opp["sl_pct"],
                                              "TRINITY", max_hours=TRINITY_MAX_HOURS)
                        if trade:
                            alt_trades.append(trade)
                            _alt_excluded = set()
                        else:
                            _alt_excluded.discard(opp["symbol"])

            # Moonshot + Reversal (parallel scan)
            reversal_strategy_paused = _strategy_paused_until.get("REVERSAL", 0) > time.time()
            non_trinity_count = sum(1 for t in alt_trades if t["label"] != "TRINITY")
            if not _paused and not session_paused and non_trinity_count < effective_alt_max:
                used_moonshot = sum(t["budget_used"] for t in alt_trades if t["label"] in ("MOONSHOT","REVERSAL","PRE_BREAKOUT"))
                available_moonshot = moonshot_capital - used_moonshot
                if available_moonshot > 0 and tickers is not None:
                    # P8: Regime-adaptive position sizing (more capital in bull, less in bear)
                    budget_regime_mult = 1.0
                    if _market_regime_mult < 0.90:
                        budget_regime_mult = 1.3  # bull: +30% budget
                    elif _market_regime_mult > 1.20:
                        budget_regime_mult = 0.6  # bear: -40% budget
                    budget = min(available_moonshot,
                                 round(total_value * get_effective_budget_pct("MOONSHOT") * budget_regime_mult, 2))
                    min_alt = MOONSHOT_MIN_NOTIONAL
                    if budget >= min_alt:
                        # BTC health gate with hysteresis (P3):
                        # Close gate at -2% (MOONSHOT_BTC_EMA_GATE)
                        # Reopen only at -1% (MOONSHOT_BTC_GATE_REOPEN) to prevent flickering
                        if _moonshot_gate_open:
                            if _btc_ema_gap_macro < MOONSHOT_BTC_EMA_GATE:
                                _moonshot_gate_open = False
                                log.info(f"[MOONSHOT] BTC gate CLOSED (1h EMA {_btc_ema_gap_macro*100:+.1f}% < {MOONSHOT_BTC_EMA_GATE*100:.0f}%)")
                        else:
                            if _btc_ema_gap_macro >= MOONSHOT_BTC_GATE_REOPEN:
                                _moonshot_gate_open = True
                                log.info(f"[MOONSHOT] BTC gate REOPENED (1h EMA {_btc_ema_gap_macro*100:+.1f}% >= {MOONSHOT_BTC_GATE_REOPEN*100:.0f}%)")
                        btc_healthy_for_moonshot = _moonshot_gate_open
                        if not btc_healthy_for_moonshot:
                            log.debug(f"[MOONSHOT] Skipped — BTC gate closed (1h EMA {_btc_ema_gap_macro*100:+.1f}%)")

                        moon_opp = None
                        if btc_healthy_for_moonshot:
                            moon_opp = find_moonshot_opportunity(tickers, budget,
                                                                  total_value,
                                                                  exclude=_alt_excluded,
                                                                  open_symbols=open_symbols)
                        # Reversal: only scan if not strategy-paused
                        rev_opp = None
                        if not reversal_strategy_paused:
                            rev_opp = find_reversal_opportunity(tickers, budget,
                                                                  exclude=_alt_excluded,
                                                                  open_symbols=open_symbols)
                        # Pick the better opportunity (reversal gets bonus in dip markets)
                        chosen_opp = None
                        chosen_label = None
                        chosen_tp = None
                        chosen_sl = None
                        chosen_hours = None
                        if moon_opp and rev_opp:
                            # Both found — prefer reversal if BTC is trending down
                            rev_bonus = 10 if _btc_ema_gap < -0.005 else 0
                            if (rev_opp.get("score", 0) + rev_bonus) > moon_opp.get("score", 0):
                                chosen_opp, chosen_label = rev_opp, "REVERSAL"
                                chosen_tp = REVERSAL_TP
                                chosen_sl = rev_opp.get("cap_sl_pct", REVERSAL_SL)
                                chosen_hours = REVERSAL_MAX_HOURS
                            else:
                                chosen_opp, chosen_label = moon_opp, "MOONSHOT"
                                chosen_tp, chosen_sl, chosen_hours = MOONSHOT_TP_INITIAL, MOONSHOT_SL, MOONSHOT_MAX_HOURS
                        elif rev_opp:
                            chosen_opp, chosen_label = rev_opp, "REVERSAL"
                            chosen_tp = REVERSAL_TP
                            chosen_sl = rev_opp.get("cap_sl_pct", REVERSAL_SL)
                            chosen_hours = REVERSAL_MAX_HOURS
                        elif moon_opp:
                            chosen_opp, chosen_label = moon_opp, "MOONSHOT"
                            chosen_tp, chosen_sl, chosen_hours = MOONSHOT_TP_INITIAL, MOONSHOT_SL, MOONSHOT_MAX_HOURS

                        if chosen_opp:
                            trade = open_position(chosen_opp, budget, chosen_tp, chosen_sl,
                                                  chosen_label, max_hours=chosen_hours)
                            if trade:
                                alt_trades.append(trade)
                                _alt_excluded = set()
                            else:
                                _alt_excluded.discard(chosen_opp["symbol"])

                        # Pre-breakout only if nothing else was found AND BTC is healthy
                        if not chosen_opp and btc_healthy_for_moonshot:
                            opp = find_prebreakout_opportunity(tickers, budget,
                                                               exclude=_alt_excluded,
                                                               open_symbols=open_symbols)
                            if opp:
                                trade = open_position(opp, budget, PRE_BREAKOUT_TP, PRE_BREAKOUT_SL,
                                                      "PRE_BREAKOUT", max_hours=PRE_BREAKOUT_MAX_HOURS)
                                if trade:
                                    alt_trades.append(trade)
                                    _alt_excluded = set()
                                else:
                                    _alt_excluded.discard(opp["symbol"])
            # Alt exits
            for trade in alt_trades[:]:
                should_exit, reason = check_exit(trade)
                if should_exit:
                    if reason in ("PARTIAL_TP", "MICRO_TP"):
                        execute_partial_tp(trade, micro=(reason == "MICRO_TP"))
                        # If FULL_CLOSE happened, remaining is 0 — remove trade
                        if trade["qty"] <= 0:
                            alt_trades.remove(trade)
                    else:
                        _alt_excluded.add(trade["symbol"])
                        if close_position(trade, reason):
                            alt_trades.remove(trade)
            send_heartbeat(balance)
            send_daily_summary(balance)
            send_weekly_summary(balance)
            # dynamic sleep
            alt_near_target = False
            if alt_trades:
                for t in alt_trades:
                    try:
                        px = ws_price(t["symbol"]) or float(
                            public_get("/api/v3/ticker/price", {"symbol": t["symbol"]})["price"]
                        )
                        pct = (px - t["entry_price"]) / t["entry_price"] * 100
                        milestones = []
                        if t.get("micro_tp_price"):
                            milestones.append((t["micro_tp_price"] / t["entry_price"] - 1) * 100)
                        if t.get("partial_tp_price"):
                            milestones.append((t["partial_tp_price"] / t["entry_price"] - 1) * 100)
                        if t.get("breakeven_act"):
                            milestones.append(t["breakeven_act"] * 100)
                        for m in milestones:
                            if abs(pct - m) < 1.0:
                                alt_near_target = True
                                break
                    except Exception:
                        pass
            if scalper_trades:
                time.sleep(2)
            elif alt_trades and alt_near_target:
                if _fast_cycle_counter < MAX_FAST_CYCLES:
                    time.sleep(3)
                    _fast_cycle_counter += 1
                else:
                    time.sleep(5)
                    _fast_cycle_counter = 0
            elif alt_trades:
                _fast_cycle_counter = 0
                time.sleep(5)
            else:
                _fast_cycle_counter = 0
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

if __name__ == "__main__":
    run()