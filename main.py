"""
MEXC Trading Bot — 5 Strategies + Adaptive Learning
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. SCALPER      — Max 3 trades (dynamic cap) | Signal-aware ATR TP/SL | 1H trend | 10min watchlist
                    TREND RSI gate | Move maturity filter | Confluence + Keltner bonuses.
  2. MOONSHOT     — Max 2 trades (dynamic) | SL -8% | Micro TP 30%@+2% → Partial 50%@+10% → 8% trail
                    Z-score volume burst | Rebound RSI relaxation | Momentum-decay exit.
  3. PRE-BREAKOUT — Via moonshot slot | +8%/-3% | Accumulation/Squeeze/Base-spring patterns
                    Enters BEFORE the spike rather than chasing it.
  4. REVERSAL     — Max 2 trades (5%) | TP +4% | SL cap-candle anchor | Oversold bounce
  5. TRINITY      — BTC/ETH/SOL dip recovery (5%) | Multi-window drop (4h/8h) | RSI 25-50
                    Exchange TP limit + bot SL | ATR-based sizing.
     Moonshot, Pre-Breakout, Reversal and Trinity share the alt slot.
  Adaptive: per-signal tracking | rolling threshold tuning | budget rebalancing | giveback analysis.
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

# ── Watchlist — universe of pairs pre-scored every 10 minutes ──
WATCHLIST_SIZE      = 30        # top N pairs by score to trade from
WATCHLIST_TTL       = 600       # seconds between full rescores (10 min, down from 30)
                                 # Shorter TTL lets the bot catch moves that start between rebuilds.
WATCHLIST_SURGE_SIZE = int(os.getenv("WATCHLIST_SURGE_SIZE", "40"))
                                 # Top N pairs by 24h abs_change added to candidate pool
                                 # alongside the normal top-by-volume 100.
                                 # These are deduplicated before scoring so no extra API cost
                                 # when both lists overlap; net new cost is ~0–15 kline fetches.

# ── BTC Rebound Detector — triggers early watchlist rebuild ────
# On a coordinated rebound day the window between "coin starts moving" and
# "coin is overbought" can be under 10 minutes. When BTC bounces hard,
# force a watchlist rebuild immediately rather than waiting for the TTL.
BTC_REBOUND_PCT          = float(os.getenv("BTC_REBOUND_PCT",          "0.01"))   # BTC up ≥1% in last 5m candle
BTC_REBOUND_CONFIRM_PCTS = float(os.getenv("BTC_REBOUND_CONFIRM_PCTS", "0.005"))  # prior candle also ≥0.5% — not a spike
WATCHLIST_REBOUND_MIN_INTERVAL = int(os.getenv("WATCHLIST_REBOUND_MIN_INTERVAL", "300"))
                                 # don't force-rebuild more than once every 5 min even during a rally

# ── Moonshot ──────────────────────────────────────────────────
ALT_MAX_TRADES      = 2
MOONSHOT_BUDGET_PCT   = float(os.getenv("MOONSHOT_BUDGET_PCT",   "0.03"))  # 3% — smaller size for wider SL
MOONSHOT_TP_INITIAL           = 0.15      # sets tp_price pre-partial-TP only; trailing stop takes over after
MOONSHOT_SL           = float(os.getenv("MOONSHOT_SL",           "0.08"))  # 8% — slippage can't kill the trade
MOONSHOT_TRAIL_PCT    = float(os.getenv("MOONSHOT_TRAIL_PCT",     "0.08"))  # trail 8% below highest after partial TP
MOONSHOT_MAX_VOL_RATIO = float(os.getenv("MOONSHOT_MAX_VOL_RATIO", "100000"))
                                   # max 24h vol = balance × this ratio
                                   # e.g. $52 → $5.2M | $1k → $100M (avoids large-caps)
MOONSHOT_MIN_VOL      = int(os.getenv("MOONSHOT_MIN_VOL", "50000"))  # raised from 5k — filters dangerous micro-caps
MOONSHOT_MIN_SCORE    = 30        # raised: need crossover OR strong vol burst, not just stale trend
MOONSHOT_MAX_RSI      = float(os.getenv("MOONSHOT_MAX_RSI",      "70"))   # overbought gate
MOONSHOT_MIN_RSI      = float(os.getenv("MOONSHOT_MIN_RSI",      "35"))   # freefall gate
MOONSHOT_RSI_ACCEL_MIN= float(os.getenv("MOONSHOT_RSI_ACCEL_MIN","60"))   # above this RSI, require acceleration
MOONSHOT_RSI_ACCEL_DELTA=float(os.getenv("MOONSHOT_RSI_ACCEL_DELTA","2")) # min RSI rise candle-over-candle to pass

# ── Moonshot rebound RSI relaxation ────────────────────────────
# On a genuine rebound, RSI rises fast across the board. Coins that pass ALL
# three rebound criteria (RSI accelerating + strong vol + vol_ratio >2×) are
# allowed through with a higher RSI ceiling instead of being rejected as "overbought".
# This is intentionally conservative — all three conditions must hold simultaneously.
MOONSHOT_REBOUND_MAX_RSI   = float(os.getenv("MOONSHOT_REBOUND_MAX_RSI",   "78"))  # ceiling when rebound confirmed
MOONSHOT_REBOUND_VOL_RATIO = float(os.getenv("MOONSHOT_REBOUND_VOL_RATIO",  "2.0")) # min vol_ratio to qualify
MOONSHOT_REBOUND_RSI_DELTA = float(os.getenv("MOONSHOT_REBOUND_RSI_DELTA",  "3.0")) # min RSI candle-over-candle rise
MOONSHOT_MIN_NOTIONAL = float(os.getenv("MOONSHOT_MIN_NOTIONAL", "2.0"))
MOONSHOT_MAX_HOURS  = 2
MOONSHOT_MIN_DAYS   = 2
MOONSHOT_NEW_DAYS   = 14
MOONSHOT_MIN_VOL_BURST = 2.5
MOONSHOT_MIN_VOL_RATIO = float(os.getenv("MOONSHOT_MIN_VOL_RATIO", "1.2"))  # require ≥ avg volume
# ── Volume Z-Score — statistically grounded burst detection ───
# Instead of a fixed "N× average" threshold, measure how many standard deviations
# the current volume is above the coin's own normal pattern. A spiky coin needs
# a bigger absolute spike to be meaningful; a stable coin needs less.
# Z-score ≥ 2.0 = volume is 2 stdev above normal (statistically unusual).
# vol_ratio floor ensures absolute magnitude: even z=3 on a near-zero volume coin is noise.
VOL_ZSCORE_MIN       = float(os.getenv("VOL_ZSCORE_MIN",       "2.0"))   # min z-score to qualify as burst
VOL_RATIO_FLOOR      = float(os.getenv("VOL_RATIO_FLOOR",      "1.5"))   # min vol_ratio alongside z-score
MOONSHOT_LIQUIDITY_RATIO = float(os.getenv("MOONSHOT_LIQUIDITY_RATIO", "200"))
                                   # min 1h vol = balance × this ratio
                                   # scales position liquidity requirement with account size
                                   # e.g. $52 → $10,400 min/hr | $1k → $200k | $10k → $2M
MOONSHOT_VOL_DIVISOR   = float(os.getenv("MOONSHOT_VOL_DIVISOR", "500000")) # vol-weighted sizing: budget_pct = min(3%, 24h_vol / divisor)
                                                                              # $500k vol → 1%, $1.5M → 3% (capped)

# ── Moonshot graduated timeout ─────────────────────────────────
# Hard clock replaced with P&L-aware timeouts:
MOONSHOT_TIMEOUT_FLAT_MINS   = 45    # exit if near-breakeven after this many minutes
MOONSHOT_TIMEOUT_MARGINAL_MINS= 60   # exit if pct < 5.0% after this many minutes
MOONSHOT_TIMEOUT_MAX_MINS    = 120   # absolute ceiling regardless of P&L
# Mid-hold vol re-check — if volume collapses the pump is over
MOONSHOT_VOL_CHECK_MINS      = 15    # start checking vol after this many minutes held
MOONSHOT_VOL_COLLAPSE_RATIO  = 0.5   # exit if current vol < 50% of avg AND trade barely up
# Partial TP — capture first leg reliably, let remainder run to full target
MOONSHOT_PARTIAL_TP_PCT      = 0.10  # sell first half at +10% (raised from 6% — better R:R with wider SL)
MOONSHOT_PARTIAL_TP_RATIO    = 0.50  # fraction to sell at stage 2 (50% of remaining after micro)
MOONSHOT_BREAKEVEN_ACT       = float(os.getenv("MOONSHOT_BREAKEVEN_ACT", "0.02"))  # move SL to entry at +2%
# Micro-partial TP — lock in small profit on the consistent +2-3% pops
# Fires before the main partial TP: sell 30% at +2%, move SL to entry.
# Remaining 70% runs for the +10% partial and beyond.
MOONSHOT_MICRO_TP_PCT        = float(os.getenv("MOONSHOT_MICRO_TP_PCT",   "0.02"))  # +2% micro TP
MOONSHOT_MICRO_TP_RATIO      = float(os.getenv("MOONSHOT_MICRO_TP_RATIO", "0.30"))  # sell 30% at micro TP

# ── Pre-Breakout Detection ────────────────────────────────────
# Enters BEFORE the spike rather than chasing it. Three patterns:
#   ACCUMULATION: volume rising, price flat — someone absorbing supply
#   SQUEEZE:      ATR at N-candle low in uptrend — coiling for breakout
#   BASE_SPRING:  support tested 2+ times with declining red volume
PRE_BREAKOUT_TP             = float(os.getenv("PRE_BREAKOUT_TP",             "0.08"))   # +8% TP (entering at base)
PRE_BREAKOUT_SL             = float(os.getenv("PRE_BREAKOUT_SL",             "0.03"))   # -3% SL (tight, below structure)
PRE_BREAKOUT_MAX_HOURS      = int(os.getenv("PRE_BREAKOUT_MAX_HOURS",        "3"))
PRE_BREAKOUT_MIN_VOL        = int(os.getenv("PRE_BREAKOUT_MIN_VOL",          "100000")) # 24h vol floor
PRE_BREAKOUT_ACCUM_CANDLES  = int(os.getenv("PRE_BREAKOUT_ACCUM_CANDLES",    "5"))      # vol rising N candles
PRE_BREAKOUT_ACCUM_PRICE_RANGE = float(os.getenv("PRE_BREAKOUT_ACCUM_PRICE_RANGE", "0.01"))  # price flat <1%
PRE_BREAKOUT_SQUEEZE_LOOKBACK  = int(os.getenv("PRE_BREAKOUT_SQUEEZE_LOOKBACK",  "20"))  # ATR low over N candles
PRE_BREAKOUT_BASE_TESTS     = int(os.getenv("PRE_BREAKOUT_BASE_TESTS",       "2"))      # min support touches

# ── Note 4 — Dead Coins: proactive liquidity blacklist ─────────
# Coins that fail the volume/spread check 3× in a row are blacklisted for 24h.
# Separate thresholds per strategy: Scalper is stricter, Moonshot hunts emerging pumps.
# The blacklist expires daily so recovering coins get a second chance.
DEAD_COIN_VOL_SCALPER     = int(os.getenv("DEAD_COIN_VOL_SCALPER",    "500000"))  # 24h vol floor for scalper
DEAD_COIN_VOL_MOONSHOT    = int(os.getenv("DEAD_COIN_VOL_MOONSHOT",   "150000"))  # looser — catching pumps
DEAD_COIN_SPREAD_MAX      = float(os.getenv("DEAD_COIN_SPREAD_MAX",   "0.003"))   # 0.3% — slippage danger above this
DEAD_COIN_CONSECUTIVE     = int(os.getenv("DEAD_COIN_CONSECUTIVE",    "3"))       # failures before blacklist
DEAD_COIN_BLACKLIST_HOURS = int(os.getenv("DEAD_COIN_BLACKLIST_HOURS","24"))      # blacklist duration

# ── Note 2 — ATR-Stepped Trailing Stop ─────────────────────────
# Instead of a single fixed trail width, the trail adjusts based on how far
# the trade has moved relative to ATR — tight when locking in, wide on runners.
# Tier 1 activates at +2×ATR profit (tighter than the static 3% activation).
# Tier 2 kicks in at +4×ATR — gives parabolic moves room to breathe.
SCALPER_TRAIL_ATR_ACTIVATE = float(os.getenv("SCALPER_TRAIL_ATR_ACTIVATE", "2.0"))  # ×ATR profit to activate trail
SCALPER_TRAIL_ATR_TIER1    = float(os.getenv("SCALPER_TRAIL_ATR_TIER1",    "1.0"))  # trail = 1×ATR at tier1
SCALPER_TRAIL_ATR_TIER2    = float(os.getenv("SCALPER_TRAIL_ATR_TIER2",    "2.0"))  # trail = 2×ATR at +4×ATR profit
SCALPER_TRAIL_TIER2_THRESH = float(os.getenv("SCALPER_TRAIL_TIER2_THRESH", "4.0"))  # ×ATR profit threshold for tier2
# MOONSHOT: same idea — widen trail after partial TP fires on big runners
MOONSHOT_TRAIL_ATR_WIDE    = float(os.getenv("MOONSHOT_TRAIL_ATR_WIDE",    "0.12")) # 12% trail after +4×ATR (vs 8% default)
MOONSHOT_TRAIL_WIDE_THRESH = float(os.getenv("MOONSHOT_TRAIL_WIDE_THRESH", "4.0"))  # ×ATR profit threshold

# ── Note 11 — Confidence-Weighted Partial TP (Scalper) ─────────
# High-confidence scalper trades (score ≥ threshold) capture a partial at the
# normal TP target, then ride the remaining 70% on a wider ATR trail — no hard cap.
SCALPER_PARTIAL_TP_SCORE     = int(os.getenv("SCALPER_PARTIAL_TP_SCORE",     "85"))
SCALPER_PARTIAL_TP_RATIO     = float(os.getenv("SCALPER_PARTIAL_TP_RATIO",   "0.30"))  # sell 30% at TP
SCALPER_PARTIAL_TP_TRAIL_MULT= float(os.getenv("SCALPER_PARTIAL_TP_TRAIL_MULT","2.0")) # remainder trail = 2×ATR

# ── Note 9 — Keltner Channel Breakout ──────────────────────────
# Stateless 15m confirmation: close > hl2 + KELTNER_ATR_MULT×ATR.
# Applied as a score bonus rather than a hard filter to avoid over-pruning.
# Disable by setting KELTNER_SCORE_BONUS=0.
KELTNER_ATR_MULT   = float(os.getenv("KELTNER_ATR_MULT",   "3.0"))
KELTNER_SCORE_BONUS= float(os.getenv("KELTNER_SCORE_BONUS","10"))

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
REVERSAL_SL_MAX          = 0.050  # hard cap — never risk more than 5% on a reversal
# Partial TP — capture reliable first bounce leg, protect remainder at breakeven
REVERSAL_PARTIAL_TP_PCT  = 0.025  # sell first half at +2.5%
REVERSAL_PARTIAL_TP_RATIO= 0.50   # fraction to sell at stage 1 (50%)

# ── Trinity ───────────────────────────────────────────────────
# Counter-trend recovery play on BTC/ETH/SOL only.
# Deep liquidity → exchange TP limit order, tight spreads, no slippage risk.
TRINITY_SYMBOLS       = ["SOLUSDT", "ETHUSDT", "BTCUSDT"]  # priority: fastest rebounders first
TRINITY_BUDGET_PCT    = float(os.getenv("TRINITY_BUDGET_PCT",   "0.05"))   # 5% of total_value
TRINITY_DROP_PCT      = float(os.getenv("TRINITY_DROP_PCT",     "0.02"))   # min 2% drop (lowered: 3% rarely happens in 8h)
TRINITY_MIN_RSI       = float(os.getenv("TRINITY_MIN_RSI",      "25"))     # oversold floor (lowered from 28)
TRINITY_MAX_RSI       = float(os.getenv("TRINITY_MAX_RSI",      "50"))     # widened: RSI 35-45 is already oversold for BTC/ETH/SOL
TRINITY_TP_ATR_MULT   = float(os.getenv("TRINITY_TP_ATR_MULT",  "1.8"))   # TP = 1.8 × ATR
TRINITY_SL_ATR_MULT   = float(os.getenv("TRINITY_SL_ATR_MULT",  "1.0"))   # SL = 1.0 × ATR
TRINITY_SL_MAX        = float(os.getenv("TRINITY_SL_MAX",       "0.025"))  # SL capped at 2.5%
TRINITY_TP_MIN        = float(os.getenv("TRINITY_TP_MIN",       "0.008"))  # TP floor (covers fees)
TRINITY_MAX_HOURS     = int(os.getenv("TRINITY_MAX_HOURS",      "6"))      # extended from 4h — recovery takes time
TRINITY_VOL_BURST     = float(os.getenv("TRINITY_VOL_BURST",    "1.2"))    # entry candle vol ≥ 1.2× avg (lowered: turns are quiet)
TRINITY_BREAKEVEN_ACT = float(os.getenv("TRINITY_BREAKEVEN_ACT","0.01"))   # lock SL to entry at +1%
# Drop lookback — check multiple windows and use the deepest drop found.
# Institutional dips on BTC/ETH/SOL play out over 6-12h, not 4h.
TRINITY_DROP_LOOKBACK_CANDLES = [16, 32]  # 4h and 8h on 15m chart
MIN_PRICE         = 0.001
SCAN_INTERVAL     = 60
STATE_FILE        = "state.json"  # persists open positions + history across restarts

# ═══════════════════════════════════════════════════════════════
#  ADAPTIVE LEARNING — Self-Tuning Systems
# ═══════════════════════════════════════════════════════════════

# ── A. Move Maturity Filter ───────────────────────────────────
# Measures WHERE in the current move the price is (0.0 = at lows, 1.0 = at highs).
# High maturity = entering late in a pump → score penalty.
# Penalty is proportional: maturity 0.80 → 0.80 × MULT × base penalty.
# "base penalty" is dynamically derived from the candidate's own score so the filter
# self-scales across volatile vs. calm conditions — no fixed constant.
MATURITY_LOOKBACK       = int(os.getenv("MATURITY_LOOKBACK",       "20"))  # candles to measure range
MATURITY_PENALTY_MULT   = float(os.getenv("MATURITY_PENALTY_MULT", "0.5"))  # fraction of score lost at maturity=1.0
MATURITY_THRESHOLD      = float(os.getenv("MATURITY_THRESHOLD",    "0.75")) # below this: no penalty
# Moonshot is more tolerant of late entries since it targets bigger moves
MATURITY_MOONSHOT_THRESHOLD = float(os.getenv("MATURITY_MOONSHOT_THRESHOLD", "0.85"))

# ── B. Momentum-Decay Exit (replaces flat VOL_COLLAPSE ratio) ─
# Instead of comparing volume to a single average, track the SLOPE of volume.
# A healthy consolidation has flat/rising vol; a dying pump has declining vol + flat price.
MOMENTUM_DECAY_CANDLES  = int(os.getenv("MOMENTUM_DECAY_CANDLES",   "4"))   # consecutive declining-vol candles
MOMENTUM_DECAY_PRICE_RANGE = float(os.getenv("MOMENTUM_DECAY_PRICE_RANGE", "0.003"))
                                   # price must also be flat (< 0.3% range) for decay to trigger
MOMENTUM_DECAY_MIN_HELD = float(os.getenv("MOMENTUM_DECAY_MIN_HELD", "10"))  # minutes before checking

# ── C. Adaptive Score Threshold ───────────────────────────────
# Rolling performance tracker that adjusts entry thresholds based on recent results.
# When the last N trades have negative Sharpe, tighten the threshold.
# When positive Sharpe, relax it (but never below the base).
# Adjustments are small (+/- 3-5 pts) and bounded to prevent runaway.
ADAPTIVE_WINDOW         = int(os.getenv("ADAPTIVE_WINDOW",         "12"))   # trades to compute rolling stats
ADAPTIVE_TIGHTEN_STEP   = float(os.getenv("ADAPTIVE_TIGHTEN_STEP", "5"))    # pts added when Sharpe < 0
ADAPTIVE_RELAX_STEP     = float(os.getenv("ADAPTIVE_RELAX_STEP",   "3"))    # pts removed when Sharpe > 0.5
ADAPTIVE_MAX_OFFSET     = float(os.getenv("ADAPTIVE_MAX_OFFSET",   "20"))   # max pts above base threshold
ADAPTIVE_MIN_OFFSET     = float(os.getenv("ADAPTIVE_MIN_OFFSET",   "-5"))   # max pts below base (conservative)

# ── D. Performance-Based Budget Allocation ────────────────────
# Every PERF_REBALANCE_TRADES completed trades, shift budget allocation toward
# whichever strategy has better Sharpe. The allocation is bounded so no strategy
# goes below a floor or above a ceiling.
PERF_REBALANCE_TRADES   = int(os.getenv("PERF_REBALANCE_TRADES",   "20"))   # rebalance after every N total trades
PERF_SCALPER_FLOOR      = float(os.getenv("PERF_SCALPER_FLOOR",    "0.10")) # scalper never below 10%
PERF_SCALPER_CEIL       = float(os.getenv("PERF_SCALPER_CEIL",     "0.40")) # scalper never above 40%
PERF_MOONSHOT_FLOOR     = float(os.getenv("PERF_MOONSHOT_FLOOR",   "0.02")) # moonshot never below 2%
PERF_MOONSHOT_CEIL      = float(os.getenv("PERF_MOONSHOT_CEIL",    "0.08")) # moonshot never above 8%
PERF_SHIFT_STEP         = float(os.getenv("PERF_SHIFT_STEP",       "0.01")) # shift 1% per rebalance

# ── E. Fee-Aware TP Floor ─────────────────────────────────────
# Instead of a fixed TP minimum, compute from actual fee tier + slippage buffer.
# MEXC market order fee = 0.1% each side (taker). VIP tiers vary.
# The TP floor = 2 × single_fee + slippage + min_profit.
# Dynamically reads from recent trade fills if available, else uses the conservative default.
FEE_RATE_TAKER          = float(os.getenv("FEE_RATE_TAKER",        "0.001"))  # 0.1% per side (MEXC default)
FEE_SLIPPAGE_BUFFER     = float(os.getenv("FEE_SLIPPAGE_BUFFER",   "0.002"))  # 0.2% assumed slippage
FEE_MIN_PROFIT          = float(os.getenv("FEE_MIN_PROFIT",        "0.010"))  # 1.0% min profit after costs

# ── F. Giveback Tracking ─────────────────────────────────────
# Logged at close time to tune trailing stops.
# Target giveback ratio: 30-35% of peak profit.
GIVEBACK_TARGET_LOW     = float(os.getenv("GIVEBACK_TARGET_LOW",    "0.25"))
GIVEBACK_TARGET_HIGH    = float(os.getenv("GIVEBACK_TARGET_HIGH",   "0.40"))

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

# ── A. Order Book Depth Check ──────────────────────────────────
# Volume can be wash-traded. Bid-side depth tells us whether we can actually
# exit at our SL price without severe slippage.
# We fetch 20 levels (vs 5 for spread check) and sum bids within
# DEPTH_PCT_RANGE of the best bid. If total bid USDT < position_value ×
# DEPTH_BID_RATIO, the order book is too thin to absorb our exit — skip.
# Set DEPTH_BID_RATIO=0 to disable. Applies to SCALPER and MOONSHOT only.
DEPTH_BID_LEVELS    = int(os.getenv("DEPTH_BID_LEVELS",    "20"))   # L2 levels to fetch
DEPTH_PCT_RANGE     = float(os.getenv("DEPTH_PCT_RANGE",   "0.02")) # sum bids within 2% of best bid
DEPTH_BID_RATIO     = float(os.getenv("DEPTH_BID_RATIO",   "3.0"))  # min bid depth = 3× position value
                                  # e.g. $50 position needs ≥$150 of bids within 2% to enter

# ── C. Reversal Flat-Progress Exit ────────────────────────────
# Mean-reversion trades have a shelf life. If the bounce hasn't made meaningful
# progress toward the TP target within REVERSAL_FLAT_MINS, the thesis is stale —
# cut the trade and redeploy capital rather than sitting in a non-moving position.
# "Progress" = (price − entry) / (tp_price − entry). At 40%, the coin has covered
# nearly half the expected bounce range; below that after 45min, call it dead.
# Does NOT apply after partial TP fires (remainder is risk-free, let it breathe).
REVERSAL_FLAT_MINS     = int(os.getenv("REVERSAL_FLAT_MINS",     "45"))   # minutes before checking
REVERSAL_FLAT_PROGRESS = float(os.getenv("REVERSAL_FLAT_PROGRESS","0.40")) # min fraction of TP range covered

# ── D. Kelly Criterion Lite — Score-Based Risk Multiplier ─────
# The existing risk model sizes by SL width (1% risk / sl_pct).
# This layer adjusts that base risk by entry conviction (score tier).
# A marginal entry (score just above threshold) gets 0.6× risk.
# A high-confluence entry (score ≥ 85, already eligible for partial TP) gets 1.2×.
# The result is always hard-capped at SCALPER_BUDGET_PCT regardless of multiplier.
# Tiers are relative to SCALPER_THRESHOLD so they auto-adjust if threshold changes.
KELLY_MULT_MARGINAL  = float(os.getenv("KELLY_MULT_MARGINAL",  "0.60"))  # score < threshold+15
KELLY_MULT_SOLID     = float(os.getenv("KELLY_MULT_SOLID",     "0.80"))  # score < threshold+30
KELLY_MULT_STANDARD  = float(os.getenv("KELLY_MULT_STANDARD",  "1.00"))  # score < threshold+45
KELLY_MULT_HIGH_CONF = float(os.getenv("KELLY_MULT_HIGH_CONF", "1.20"))  # score ≥ threshold+45
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
_liquidity_blacklist: dict = {}   # {symbol: until_ts} — dead coin blacklist, expires after 24h
_liquidity_fail_count: dict = {}  # {symbol: int} — consecutive scan failures before blacklist
_scanner_log_buffer   = collections.deque(maxlen=5)  # rolling window, auto-evicts oldest
_paused               = False

# Rotation scan cooldown — don't hammer 40+ API calls every 5s
_last_rotation_scan    = 0.0
ROTATION_SCAN_INTERVAL = 30  # seconds between rotation scans

# ── Adaptive learning state ───────────────────────────────────
# Per-strategy threshold offsets — persist across restarts.
# Positive = stricter than base, negative = more lenient.
_adaptive_offsets: dict = {"SCALPER": 0.0, "MOONSHOT": 0.0}
# Track the trade count at which we last rebalanced budgets
_last_rebalance_count  = 0
# Dynamic budget overrides — computed by perf-based allocation
# None means "use the static config value"
_dynamic_scalper_budget: float | None  = None
_dynamic_moonshot_budget: float | None = None

# New listings cache — scanning 60 symbols takes 3+ seconds, cache for 5 min
_new_listings_cache    = []
_new_listings_cache_at = 0.0
NEW_LISTINGS_CACHE_TTL = 300  # seconds

# Watchlist — top WATCHLIST_SIZE pairs pre-scored every WATCHLIST_TTL seconds
# During normal scans we only evaluate these, saving hundreds of API calls per hour
_watchlist             = []   # list of scored candidate dicts
_watchlist_at          = 0.0  # timestamp of last full rebuild
_last_rebound_rebuild  = 0.0  # timestamp of last BTC-rebound-triggered rebuild
                               # guards against rebuilding more than once per WATCHLIST_REBOUND_MIN_INTERVAL

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
            "paused":               _paused,
            "scalper_excluded":     _scalper_excluded,
            "alt_excluded":         list(_alt_excluded),
            "api_blacklist":        list(_api_blacklist),
            "liquidity_blacklist":  _liquidity_blacklist,
            "liquidity_fail_count": _liquidity_fail_count,
            # ── Adaptive learning state ──
            "adaptive_offsets":       _adaptive_offsets,
            "last_rebalance_count":   _last_rebalance_count,
            "dynamic_scalper_budget": _dynamic_scalper_budget,
            "dynamic_moonshot_budget":_dynamic_moonshot_budget,
            "saved_at":             datetime.now(timezone.utc).isoformat(),
        }
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(payload, f, default=str)
        os.replace(tmp, STATE_FILE)  # atomic on POSIX; avoids corrupt half-writes
    except Exception as e:
        log.warning(f"State save failed: {e}")


def load_state() -> tuple:
    """
    Load persisted state from STATE_FILE.
    Returns (scalper_trades, alt_trades, trade_history,
             consecutive_losses, win_rate_pause_until, streak_paused_at,
             paused, scalper_excluded, alt_excluded, api_blacklist,
             liquidity_blacklist, liquidity_fail_count,
             adaptive_offsets, last_rebalance_count,
             dynamic_scalper_budget, dynamic_moonshot_budget).
    Returns empty defaults if file is missing or unreadable.
    """
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
        # Try direct JSON parse first (most reliable when model follows instructions).
        # Fall back to extracting the first balanced {...} block for preamble cases.
        parsed = None
        try:
            parsed = json.loads(text)
        except json.JSONDecodeError:
            # Walk the string to find the outermost balanced {...} block.
            # Non-greedy regex like r'\{.*?\}' breaks on nested structures like
            # {"coins": [{"symbol": ...}]} — it stops at the first inner '}'.
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


def check_dead_coin(symbol: str, vol_24h: float, spread: float,
                    strategy: str = "SCALPER") -> bool:
    """
    Note 4 — Dead Coins: proactive liquidity health check.

    Called during scanner runs for each candidate. Tracks consecutive failures
    and blacklists symbols that fail DEAD_COIN_CONSECUTIVE times in a row.
    The blacklist expires after DEAD_COIN_BLACKLIST_HOURS so recovering coins
    (e.g., a coin that gets relisted or suddenly pumps) get a second chance.

    Returns True if the coin is dead (should be skipped), False if healthy.
    Never raises — any error returns False (don't block on a health check).
    """
    global _liquidity_blacklist, _liquidity_fail_count

    # Already blacklisted?
    until_ts = _liquidity_blacklist.get(symbol)
    if until_ts:
        if time.time() < until_ts:
            return True  # still in blacklist window
        else:
            # Expired — give the coin a second chance
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
        # Healthy scan — reset the failure counter
        _liquidity_fail_count.pop(symbol, None)
        return False


def keltner_breakout(df: pd.DataFrame,
                     atr_mult: float = None) -> bool:
    """
    Note 9 — Stateless 15m Keltner Channel breakout confirmation.

    True if the latest close is above the upper channel: close > hl2 + mult×ATR.
    Requires no persistent state — safe to call on any klines DataFrame.
    Returns False on any error so it never blocks an entry.
    """
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
    """Wilder's RSI using EWM (alpha=1/period) — matches MEXC chart values.
    SMA-based rolling mean gives systematically different RSI readings that
    cause gate mismatches versus what traders see on the exchange."""
    delta = series.diff()
    gain  = delta.clip(lower=0).ewm(alpha=1.0 / period, adjust=False).mean()
    loss  = (-delta.clip(upper=0)).ewm(alpha=1.0 / period, adjust=False).mean()
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


def calc_vol_zscore(volume: pd.Series, lookback: int = 20) -> float:
    """
    Compute the z-score of the latest candle's volume relative to the
    preceding `lookback` candles.

    z = (current_vol - mean) / stdev

    A coin with erratic volume (high stdev) needs a larger absolute spike
    to produce a high z-score — this automatically filters out coins where
    6× volume is routine noise vs. coins where 3× is genuinely unusual.

    Returns 0.0 on any error or insufficient data (never blocks).
    """
    try:
        if len(volume) < lookback + 1:
            return 0.0
        window  = volume.iloc[-(lookback + 1):-1]  # exclude current candle
        current = float(volume.iloc[-1])
        mean    = float(window.mean())
        std     = float(window.std())
        if std <= 0 or mean <= 0:
            return 0.0
        return (current - mean) / std
    except Exception:
        return 0.0


# ── Move Maturity Filter ─────────────────────────────────────

def calc_move_maturity(df: pd.DataFrame, lookback: int = None) -> float:
    """
    Measure where in the current move the price sits (0.0–1.0).

    0.0 = price at the bottom of the recent range (early/dip entry)
    1.0 = price at the top of the recent range (late/chasing entry)

    Uses high/low of the last `lookback` candles to define the range.
    Returns 0.5 on any error so it never blocks an entry.
    """
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
            return 0.5  # zero range — flat, no meaningful maturity
        return max(0.0, min(1.0, (current - low) / (high - low)))
    except Exception:
        return 0.5


def maturity_penalty(maturity: float, raw_score: float,
                     threshold: float = None) -> float:
    """
    Score penalty for entering late in a move.

    Dynamically proportional: the penalty scales with the candidate's OWN score
    so that a 90-score candidate in a late move gets a larger absolute penalty
    than a 45-score candidate — but both lose the same *fraction* of their score.

    No penalty below the threshold (default: MATURITY_THRESHOLD).
    """
    if threshold is None:
        threshold = MATURITY_THRESHOLD
    if maturity <= threshold:
        return 0.0
    # How far past the threshold (0.0–1.0 normalized)
    overshoot = (maturity - threshold) / (1.0 - threshold) if threshold < 1.0 else 0.0
    # Penalty = fraction of the raw score
    penalty = raw_score * MATURITY_PENALTY_MULT * overshoot
    return round(penalty, 1)


# ── Momentum-Decay Detection ─────────────────────────────────

def detect_momentum_decay(symbol: str, min_candles: int = None,
                          price_range: float = None) -> bool:
    """
    True if a pump is dying: volume declining over N consecutive candles
    while price is flat (range < threshold).

    Replaces the old single-candle VOL_COLLAPSE ratio check which was too
    aggressive and triggered on normal consolidation patterns.
    """
    if min_candles is None:
        min_candles = MOMENTUM_DECAY_CANDLES
    if price_range is None:
        price_range = MOMENTUM_DECAY_PRICE_RANGE
    try:
        # Need min_candles + 1 candles to check N consecutive declines
        needed = max(min_candles + 2, 8)
        df = parse_klines(symbol, interval="5m", limit=needed + 5, min_len=needed)
        if df is None:
            return False

        vol   = df["volume"].iloc[-(min_candles + 1):]
        close = df["close"].iloc[-min_candles:]

        # Check volume declining for N consecutive candles
        vol_vals = vol.values
        declining = all(
            float(vol_vals[i + 1]) < float(vol_vals[i])
            for i in range(len(vol_vals) - 1)
        )
        if not declining:
            return False

        # Check price is flat — range of last N candles < threshold
        close_vals  = [float(c) for c in close.values]
        price_high  = max(close_vals)
        price_low   = min(close_vals)
        mid         = (price_high + price_low) / 2 if (price_high + price_low) > 0 else 1.0
        flat_range  = (price_high - price_low) / mid

        if flat_range >= price_range:
            return False  # price is still moving — not a decay, just volume normalising

        log.info(f"📉 [MOMENTUM_DECAY] {symbol} — vol declining {min_candles} candles, "
                 f"price range {flat_range*100:.3f}%")
        return True
    except Exception:
        return False


# ── Adaptive Threshold System ─────────────────────────────────

def update_adaptive_thresholds():
    """
    Adjust entry score thresholds based on rolling per-strategy performance.

    Called after every close_position. Reads trade_history, computes a rolling
    Sharpe over the last ADAPTIVE_WINDOW trades per strategy, and shifts the
    threshold offset:
      - Sharpe < 0  → tighten by ADAPTIVE_TIGHTEN_STEP (entries are bad)
      - Sharpe > 0.5 → relax by ADAPTIVE_RELAX_STEP (entries are good)
      - Otherwise   → no change (wait for clearer signal)

    Also logs per-signal win rates so /metrics can surface which signals
    are consistently profitable vs. which are dragging performance.

    Offsets are bounded by ADAPTIVE_MAX_OFFSET / ADAPTIVE_MIN_OFFSET.
    """
    global _adaptive_offsets

    for strategy in ("SCALPER", "MOONSHOT"):
        full = [t for t in trade_history
                if t.get("label") == strategy
                and not t.get("is_partial")][-ADAPTIVE_WINDOW:]
        if len(full) < max(5, ADAPTIVE_WINDOW // 2):
            continue  # not enough data to be statistically meaningful

        pnls = [t["pnl_pct"] for t in full]
        n    = len(pnls)
        mean = sum(pnls) / n
        if n > 1:
            var   = sum((p - mean) ** 2 for p in pnls) / (n - 1)
            std   = var ** 0.5
            sharpe = (mean / std) if std > 0 else 0.0
        else:
            sharpe = 0.0

        old_offset = _adaptive_offsets.get(strategy, 0.0)
        if sharpe < 0:
            new_offset = min(old_offset + ADAPTIVE_TIGHTEN_STEP, ADAPTIVE_MAX_OFFSET)
            direction  = "tightened"
        elif sharpe > 0.5:
            new_offset = max(old_offset - ADAPTIVE_RELAX_STEP, ADAPTIVE_MIN_OFFSET)
            direction  = "relaxed"
        else:
            new_offset = old_offset
            direction  = "unchanged"

        if new_offset != old_offset:
            _adaptive_offsets[strategy] = new_offset

            # Per-signal breakdown for the log — shows which signals are working
            signal_stats = _compute_signal_stats(full)
            signal_summary = " | ".join(
                f"{sig}:{s['wins']}W/{s['total']-s['wins']}L"
                for sig, s in sorted(signal_stats.items())
                if s["total"] >= 2
            )

            log.info(f"🧠 [ADAPTIVE] {strategy} threshold {direction}: "
                     f"offset {old_offset:+.0f} → {new_offset:+.0f} "
                     f"(Sharpe={sharpe:.2f} over {n} trades)"
                     + (f" [{signal_summary}]" if signal_summary else ""))


def _compute_signal_stats(trades: list) -> dict:
    """
    Compute per-signal win rate and P&L from a list of trades.
    Returns {signal: {total, wins, losses, avg_pnl, win_rate}}.
    Shared by update_adaptive_thresholds and _compute_metrics.
    """
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

    # Compute derived stats
    for sig, s in by_signal.items():
        s["avg_pnl"]  = round(s["pnl_sum"] / s["total"], 2) if s["total"] > 0 else 0.0
        s["win_rate"] = round(s["wins"] / s["total"] * 100, 1) if s["total"] > 0 else 0.0
        del s["pnl_list"]  # don't carry raw data forward
    return by_signal


def get_effective_threshold(strategy: str) -> float:
    """
    Return the current entry threshold for a strategy,
    incorporating the adaptive offset.
    """
    base = {"SCALPER": SCALPER_THRESHOLD, "MOONSHOT": MOONSHOT_MIN_SCORE}.get(strategy, 40)
    offset = _adaptive_offsets.get(strategy, 0.0)
    return base + offset


# ── Performance-Based Budget Allocation ───────────────────────

def rebalance_budgets():
    """
    Shift capital allocation between strategies based on rolling performance.

    Computes Sharpe for each strategy over the last PERF_REBALANCE_TRADES.
    The strategy with higher Sharpe gets a budget bump; the other gets trimmed.
    Both are clamped to floor/ceiling to ensure neither strategy starves.

    Only fires after every PERF_REBALANCE_TRADES total completed trades.
    """
    global _last_rebalance_count, _dynamic_scalper_budget, _dynamic_moonshot_budget

    full = [t for t in trade_history if not t.get("is_partial")]
    if len(full) < PERF_REBALANCE_TRADES or len(full) <= _last_rebalance_count:
        return
    if len(full) - _last_rebalance_count < PERF_REBALANCE_TRADES:
        return

    _last_rebalance_count = len(full)

    def strategy_sharpe(label: str) -> float:
        st = [t for t in full if t.get("label") == label][-PERF_REBALANCE_TRADES:]
        if len(st) < 5:
            return 0.0
        pnls = [t["pnl_pct"] for t in st]
        mean = sum(pnls) / len(pnls)
        if len(pnls) > 1:
            var = sum((p - mean) ** 2 for p in pnls) / (len(pnls) - 1)
            std = var ** 0.5
            return (mean / std) if std > 0 else 0.0
        return 0.0

    scalper_sharpe  = strategy_sharpe("SCALPER")
    moonshot_sharpe = strategy_sharpe("MOONSHOT")

    # Current budgets (use dynamic if set, else static)
    curr_scalper  = _dynamic_scalper_budget  or SCALPER_BUDGET_PCT
    curr_moonshot = _dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT

    if scalper_sharpe > moonshot_sharpe + 0.2:
        # Scalper outperforming → shift toward scalper
        new_scalper  = min(PERF_SCALPER_CEIL,  curr_scalper  + PERF_SHIFT_STEP)
        new_moonshot = max(PERF_MOONSHOT_FLOOR, curr_moonshot - PERF_SHIFT_STEP)
    elif moonshot_sharpe > scalper_sharpe + 0.2:
        # Moonshot outperforming → shift toward moonshot
        new_scalper  = max(PERF_SCALPER_FLOOR,  curr_scalper  - PERF_SHIFT_STEP)
        new_moonshot = min(PERF_MOONSHOT_CEIL,  curr_moonshot + PERF_SHIFT_STEP)
    else:
        # Similar performance — no shift
        new_scalper  = curr_scalper
        new_moonshot = curr_moonshot

    if new_scalper != curr_scalper or new_moonshot != curr_moonshot:
        _dynamic_scalper_budget  = new_scalper
        _dynamic_moonshot_budget = new_moonshot
        log.info(f"💼 [REBALANCE] Scalper: {curr_scalper*100:.0f}% → {new_scalper*100:.0f}% "
                 f"(Sharpe {scalper_sharpe:.2f}) | "
                 f"Moonshot: {curr_moonshot*100:.0f}% → {new_moonshot*100:.0f}% "
                 f"(Sharpe {moonshot_sharpe:.2f})")
        telegram(
            f"💼 <b>Budget Rebalanced</b>\n"
            f"━━━━━━━━━━━━━━━\n"
            f"🟢 Scalper: {new_scalper*100:.0f}% (Sharpe {scalper_sharpe:.2f})\n"
            f"🌙 Moonshot: {new_moonshot*100:.0f}% (Sharpe {moonshot_sharpe:.2f})\n"
            f"Based on last {PERF_REBALANCE_TRADES} trades"
        )


def get_effective_budget_pct(strategy: str) -> float:
    """Return the current effective budget pct, using dynamic override if set."""
    if strategy == "SCALPER":
        return _dynamic_scalper_budget or SCALPER_BUDGET_PCT
    elif strategy == "MOONSHOT":
        return _dynamic_moonshot_budget or MOONSHOT_BUDGET_PCT
    return SCALPER_BUDGET_PCT


# ── Fee-Aware TP Floor ────────────────────────────────────────

def calc_fee_aware_tp_floor() -> float:
    """
    Compute the minimum TP percentage that covers round-trip fees + slippage + min profit.

    Dynamically estimates from recent trade fills if available (actual fee rates
    may differ from default if user has VIP tier or MX deduction).
    Falls back to conservative FEE_RATE_TAKER constant.
    """
    # Try to estimate actual fee rate from recent trades
    recent_with_fees = [t for t in trade_history
                        if t.get("fee_usdt", 0) > 0 and t.get("cost_usdt", 0) > 0][-10:]
    if len(recent_with_fees) >= 3:
        # Average fee as fraction of cost — covers both buy and sell sides
        avg_fee_pct = sum(t["fee_usdt"] / t["cost_usdt"]
                          for t in recent_with_fees) / len(recent_with_fees)
        # This is already round-trip (buy + sell fees are both in fee_usdt)
        effective_fee = avg_fee_pct
    else:
        # Conservative default: 2 × single-side taker fee
        effective_fee = 2 * FEE_RATE_TAKER

    floor = effective_fee + FEE_SLIPPAGE_BUFFER + FEE_MIN_PROFIT
    return round(floor, 4)


# ── Entry Signal Classification ───────────────────────────────

def classify_entry_signal(crossed_now: bool = False, vol_ratio: float = 1.0,
                          rsi: float = 50.0, is_new: bool = False,
                          is_trending: bool = False,
                          label: str = "SCALPER") -> str:
    """
    Classify the dominant entry signal driving a trade.

    Used by:
      - _score_scalper / _score_moonshot to tag the opp dict
      - calc_dynamic_tp_sl to select TP/SL multipliers (replacing duplicated if/elif)
      - update_adaptive_thresholds for per-signal performance tracking

    Signal priority (first match wins, same order as TP/SL classification):
      CROSSOVER  — fresh EMA9/21 crossover (strongest momentum confirmation)
      VOL_SPIKE  — volume ≥3× average (scalper) or burst detected (moonshot)
      OVERSOLD   — RSI < 40 (mean-reversion entry)
      TRENDING   — socially trending coin (moonshot only)
      NEW_LISTING— recently listed coin (moonshot only)
      TREND      — default: price trending above EMAs but no fresh signal

    REVERSAL and TRINITY have fixed signals set by their own scorers.
    """
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


# ── Signal → TP/SL multiplier mapping ────────────────────────

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

    # ── TREND signal RSI gate — block entries with decaying momentum ──
    # TREND is the weakest signal (no crossover, no vol spike, not oversold).
    # Without a catalyst, require RSI to at least be rising — entering a naked
    # trend with falling RSI is chasing a dying move. Stronger signals (CROSSOVER,
    # VOL_SPIKE, OVERSOLD) have their own catalyst and skip this check.
    if strict and not crossed_now and vol_ratio < 3.0 and rsi >= 40:
        if rsi_delta < 1.0:
            log.debug(f"[SCALPER] Skip {sym} — TREND signal with declining RSI "
                      f"(delta {rsi_delta:+.1f})")
            return None

    # Confluence bonus — non-linear reward when all three signals align simultaneously.
    # A fresh crossover alone scores 30. A vol spike alone scores 30. But when both
    # fire together with rising RSI momentum, this is a regime shift, not three
    # independent signals — deserves a material bonus on top.
    confluence_bonus = (SCALPER_CONFLUENCE_BONUS
                        if crossed_now and vol_ratio > 2.0 and rsi_delta > 0
                        else 0.0)

    score          = rsi_score + ma_score + vol_score + confluence_bonus - ema50_penalty

    # ── Move Maturity Filter — penalise late entries ──────────
    move_mat = calc_move_maturity(df5m, MATURITY_LOOKBACK)
    mat_pen  = maturity_penalty(move_mat, max(score, 1.0), MATURITY_THRESHOLD)
    score    = score - mat_pen

    # Use adaptive threshold in strict mode (entry), base threshold for watchlist
    eff_threshold = get_effective_threshold("SCALPER") if strict else max(5, SCALPER_THRESHOLD // 2)
    threshold     = eff_threshold
    if score < threshold:
        if mat_pen > 0:
            log.debug(f"[SCALPER] Skip {sym} — maturity {move_mat:.2f} penalty -{mat_pen:.1f}pts")
        elif ema50_penalty > 0:
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
        # Only fetch sentiment when score is close enough to the threshold that
        # sentiment could flip the decision. If score is already well above the
        # maximum possible penalty (SENTIMENT_MAX_PENALTY), sentiment can't push
        # it below threshold — skip the API call entirely.
        # Conversely if score is far below threshold even the max bonus can't save it.
        eff_thresh = get_effective_threshold("SCALPER")
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

    # ── Note 9 — Keltner Channel breakout bonus (strict mode only) ──
    # Fetch 15m klines once for the confirmation check — cached so no extra API hit
    # when build_watchlist and find_scalper_opportunity run close together.
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
    Called every WATCHLIST_TTL seconds (10 min) or on BTC rebound detection.
    Between rebuilds, the scalper only evaluates pairs already on the watchlist.
    8 workers (up from 5) keeps rebuild time under 30s with the larger dual-lens
    candidate pool while staying within MEXC's rate limits.
    """
    global _watchlist, _watchlist_at

    df = tickers.copy()
    df = df[df["quoteVolume"] >= SCALPER_MIN_VOL]
    df = df[df["lastPrice"]   >= SCALPER_MIN_PRICE]
    df = df[df["abs_change"]  >= SCALPER_MIN_CHANGE]
    df = df[~df["symbol"].isin(_api_blacklist)]
    # Note 4 — filter out dead coins that have been consecutively failing health checks
    now_ts = time.time()
    df = df[~df["symbol"].apply(lambda s: _liquidity_blacklist.get(s, 0) > now_ts)]

    # ── Dual-lens candidate selection ──────────────────────────
    # Normal markets: top-by-volume catches liquid trending pairs.
    # Rebound / breakout days: top-by-abs_change surfaces coins just starting
    # to move before their volume has had time to accumulate.
    # Both paths share the same SCALPER_MIN_VOL floor, so thin coins never enter.
    # Deduplication preserves order: change-movers first so they get scored even
    # if we hit the ThreadPoolExecutor queue limit.
    by_vol    = df.sort_values("quoteVolume", ascending=False).head(100)["symbol"].tolist()
    by_change = df.sort_values("abs_change",  ascending=False).head(WATCHLIST_SURGE_SIZE)["symbol"].tolist()
    candidates = list(dict.fromkeys(by_change + by_vol))  # deduped; change-movers prioritised

    log.info(f"📋 [WATCHLIST] Building from {len(candidates)} candidates "
             f"({len(by_change)} top-movers + {len(by_vol)} top-volume, deduped)...")

    # Age filter — exclude symbols that are too new for scalping.
    # Reuse the moonshot new-listings cache (already populated) rather than
    # fetching 120 daily klines one by one, which blocks for ~6 seconds.
    new_listing_syms = {n["symbol"] for n in _new_listings_cache}
    established = [s for s in candidates if s not in new_listing_syms]
    log.info(f"📋 [WATCHLIST] {len(established)} established pairs after age filter "
             f"({len(candidates) - len(established)} new listings excluded)")

    # Score all in parallel — entry scorer re-evaluates top 5 with fresh data anyway
    # Note 4: build a fast vol lookup from the tickers df so check_dead_coin can run
    # per symbol without extra API calls (spread check happens at open_position already).
    ticker_vol = dict(zip(tickers["symbol"], tickers["quoteVolume"].fillna(0)))

    scores = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        futures = {ex.submit(_score_scalper, sym, False): sym for sym in established}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result and result["score"] >= WATCHLIST_MIN_SCORE:
                    # Dead-coin check: use 24h vol from tickers; spread=0 here since
                    # a full order-book fetch per symbol would be too slow at watchlist
                    # build time — the spread gate at open_position is the real guard.
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
                f"Signal: {best.get('entry_signal','?')} | "
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

    # Dynamic liquidity threshold — scales with account size so position risk stays
    # proportional at any balance level. Uses total_value (passed as balance here)
    # so the threshold doesn't shrink when capital is temporarily deployed.
    min_1h_vol = max(5_000, balance * MOONSHOT_LIQUIDITY_RATIO)
    max_vol    = max(5_000_000, balance * MOONSHOT_MAX_VOL_RATIO)
    log.debug(f"🌙 [MOONSHOT] Vol window: ${min_1h_vol:,.0f}/hr – ${max_vol:,.0f}/day "
              f"(balance ${balance:.0f})")

    df = tickers.copy()
    df = df[df["quoteVolume"] >= MOONSHOT_MIN_VOL]
    df = df[df["quoteVolume"] <= max_vol]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]

    # Sort by absolute price change to surface anything moving hard in either direction.
    # We deliberately drop the 24h priceChangePercent directional filter here —
    # in a down market a coin can pump +100% in an hour but still show negative 24h change,
    # so filtering on 24h change misses the exact moves moonshot exists to catch.
    # head(40) instead of head(20): on a broad rebound day 20 pairs isn't enough — the
    # best early-stage mover may sit in slots 25-35 while the top 20 are already extended.
    # The kline scorer (EMA crossover + vol ratio + RSI gates) handles quality filtering.
    momentum_candidates = (df.assign(abs_change=df["priceChangePercent"].abs())
                             .sort_values("abs_change", ascending=False)
                             .head(40)["symbol"].tolist())

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

    # Pre-build O(1) lookups from the tickers df — avoids repeated O(n) pandas
    # row searches inside the parallel _score_moonshot threads.
    ticker_vol_map    = dict(zip(df["symbol"], df["quoteVolume"].fillna(0)))
    ticker_change_map = dict(zip(df["symbol"], df["priceChangePercent"].fillna(0)))

    # Score candidates in parallel with a Semaphore to avoid MEXC rate-limit (429).
    # Max 5 concurrent kline fetches — aggressive enough to be fast, gentle on the API.
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
        rsi_prev  = calc_rsi(close.iloc[:-1])  # RSI one candle ago
        rsi_delta = rsi - rsi_prev if not np.isnan(rsi_prev) else 0.0

        # ── Volume ratio — computed once, shared by rebound gate + scorer ──
        avg_vol   = float(volume.iloc[-20:-1].mean()) if len(volume) >= 21 else 0.0
        vol_ratio = (float(volume.iloc[-1]) / avg_vol) if avg_vol > 0 else 1.0

        # ── Rebound context detection ────────────────────────────
        # A genuine market-wide rebound pushes RSI up fast across ALL coins.
        # If RSI is accelerating strongly AND volume is surging (both must hold),
        # we're likely in the early leg of a move — not a late exhausted pump.
        # In that case, allow RSI up to MOONSHOT_REBOUND_MAX_RSI (78) instead of 70.
        # All three conditions must be true simultaneously to prevent misfires:
        #   1. RSI delta > threshold — momentum genuinely accelerating
        #   2. vol_ratio > threshold — real buying pressure, not just price drift
        #   3. RSI within the extended ceiling — not already fully extended
        is_rebound_context = (
            rsi_delta  >= MOONSHOT_REBOUND_RSI_DELTA   # RSI rising fast
            and vol_ratio >= MOONSHOT_REBOUND_VOL_RATIO  # real volume behind it
            and rsi <= MOONSHOT_REBOUND_MAX_RSI          # not already fully extended
        )
        effective_max_rsi = MOONSHOT_REBOUND_MAX_RSI if is_rebound_context else MOONSHOT_MAX_RSI

        if rsi > effective_max_rsi:
            return None  # overbought — entering after the bulk of the move
        if rsi < MOONSHOT_MIN_RSI:
            return None  # freefall — coin declining, not starting to pump

        if is_rebound_context and rsi > MOONSHOT_MAX_RSI:
            log.debug(f"[MOONSHOT] {sym} rebound RSI gate: {rsi:.1f} allowed "
                      f"(delta={rsi_delta:+.1f} vol={vol_ratio:.1f}× — rebound context)")
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
        # avg_vol and vol_ratio already computed above for the rebound RSI gate — reuse them.
        vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0
        if vol_ratio < MOONSHOT_MIN_VOL_RATIO:
            return None  # below average volume — no momentum
        # Recent 1h liquidity check — mirrors SCALPER_MIN_1H_VOL.
        # A coin can have $200k 24h volume but $190k happened 18h ago.
        # Candle count depends on interval: 4×15m = 1h, 1×60m = 1h.
        recent_candles = 1 if is_new else 4  # 60m interval for new listings, 15m otherwise
        recent_1h_vol = float(volume.iloc[-recent_candles:].sum()) * float(close.iloc[-1])
        if recent_1h_vol < min_1h_vol:
            log.debug(f"[MOONSHOT] Skip {sym} — dead recently "
                      f"(1h vol ${recent_1h_vol:,.0f} < ${min_1h_vol:,.0f})")
            return None
        score     = rsi_score + ma_score + vol_score

        # ── Move Maturity Filter — penalise late moonshot entries ──
        moon_maturity = calc_move_maturity(df_k, MATURITY_LOOKBACK)
        moon_mat_pen  = maturity_penalty(moon_maturity, max(score, 1.0),
                                          MATURITY_MOONSHOT_THRESHOLD)
        score = score - moon_mat_pen

        eff_moon_thresh = get_effective_threshold("MOONSHOT")
        if score < eff_moon_thresh:
            if moon_mat_pen > 0:
                log.debug(f"[MOONSHOT] Skip {sym} — maturity {moon_maturity:.2f} "
                          f"penalty -{moon_mat_pen:.1f}pts")
            return None
        # ── Note 9 — Keltner bonus on the same klines already fetched ──
        keltner_bonus = 0.0
        if KELTNER_SCORE_BONUS > 0 and keltner_breakout(df_k):
            keltner_bonus = KELTNER_SCORE_BONUS
        # Only apply sentiment/social when score is near threshold — reduces cost
        # significantly since most candidates fail well before sentiment matters.
        if score > eff_moon_thresh - 5:
            sentiment_delta, _ = sentiment_score_adjustment(sym)
            social_boost, social_summary = get_social_boost(sym)
        else:
            sentiment_delta, social_boost, social_summary = 0.0, 0.0, ""
        final_score = round(score + keltner_bonus + sentiment_delta + social_boost, 2)
        if final_score < eff_moon_thresh:
            return None
        # Note 4 — dead coin check using 24h vol from pre-built ticker lookup
        row_vol = ticker_vol_map.get(sym, 0.0)
        if check_dead_coin(sym, row_vol, 0.0, "MOONSHOT"):
            return None
        # 24h change — kept for logging only, not used as a filter.
        # EMA crossover + vol_ratio in the scorer already enforce upward momentum.
        change_1h = ticker_change_map.get(sym, 0.0)
        # Volume z-score — how unusual is this spike for THIS specific coin?
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

    # Burst detection — z-score based: is this spike statistically unusual for THIS coin?
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

        # Price burst — how big is the current candle relative to recent candles?
        safe_opens  = opens.replace(0, np.nan)
        candle_moves= (close - opens).abs() / safe_opens * 100
        avg_move    = candle_moves.iloc[-11:-1].mean()
        price_burst = (float(candle_moves.iloc[-1]) / avg_move) if avg_move > 0 else 1.0
        greens      = sum(1 for i in [-2, -1] if close.iloc[i] > opens.iloc[i])

        # Volume check: require EITHER statistically significant volume spike
        # (z-score ≥ threshold AND absolute vol_ratio above floor) OR strong price burst.
        # Z-score adapts per coin: a spiky coin needs bigger absolute spike to qualify.
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
    cap_sl_pct  = min(cap_sl_pct, REVERSAL_SL_MAX)  # never risk more than 5% on a reversal

    return {
        "symbol":      sym,
        "price":       entry_est,
        "rsi":         round(rsi, 2),
        "entry_signal":"CAPITULATION_BOUNCE",
        # Composite score: lower RSI = more oversold (better), higher recovery/vol = stronger signal.
        # Inverted RSI so sorting ascending by score gives best candidates first.
        "score":       round((REVERSAL_MAX_RSI - rsi) + recovery * 20 + (curr_vol / avg_vol if avg_vol > 0 else 1.0), 2),
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

    tradeable.sort(key=lambda x: x["score"], reverse=True)  # highest composite score first
    best = tradeable[0]
    last_top_alt = best
    scanner_log(f"🔄 [REVERSAL] Top: {best['symbol']} | RSI: {best['rsi']} | "
                f"Recovery: {best.get('recovery',0)*100:.0f}% | "
                f"BounceVol: {best.get('bounce_vol_ratio',0):.1f}× | "
                f"SL: -{best.get('cap_sl_pct',REVERSAL_SL)*100:.1f}%")

    return pick_tradeable(tradeable, budget, "REVERSAL")


# ── Scanner: Pre-Breakout ─────────────────────────────────────

def evaluate_prebreakout_candidate(sym: str) -> dict | None:
    """
    Detect accumulation/compression patterns that precede breakouts.

    Instead of chasing volume spikes (entering at the top), this identifies
    the pressure building BEFORE the explosion and positions at the base.

    Three independent patterns (first match wins):

    1. ACCUMULATION: volume rising over N candles but price flat (<1% range).
       Someone is buying large quantities without moving the price — absorbing
       sell orders patiently. When sellers exhaust, price breaks upward.

    2. SQUEEZE: ATR contracts to its lowest point in 20 candles AND price is
       above EMA21. Volatility compression in an uptrend almost always resolves
       with an explosive move upward (65-70% probability).

    3. BASE_SPRING: price tests a support level 2+ times in the last 30 candles
       with declining red-candle volume on each test. Sellers are exhausting —
       the next volume burst off this base is the real move.

    Returns an opp dict with entry_signal set to the pattern name, or None.
    """
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
        return None  # not in the right zone — overbought or freefalling

    ema21 = calc_ema(close, 21)
    above_ema21 = price_now > float(ema21.iloc[-1])

    atr     = calc_atr(df, period=14)
    atr_pct = atr / price_now if price_now > 0 else 0.01

    pattern = None
    score   = 0.0

    # ── Pattern 1: ACCUMULATION ───────────────────────────────
    # Volume rising for N candles, price essentially flat
    n = PRE_BREAKOUT_ACCUM_CANDLES
    if len(volume) >= n + 2:
        recent_vol = volume.iloc[-(n + 1):]
        vol_vals   = [float(v) for v in recent_vol.values]
        # Check volume is generally rising (at least N-1 of N steps are up)
        vol_ups = sum(1 for i in range(len(vol_vals) - 1) if vol_vals[i + 1] > vol_vals[i])
        if vol_ups >= n - 1:
            # Check price range over same window is tight
            recent_close = [float(c) for c in close.iloc[-(n + 1):].values]
            p_high, p_low = max(recent_close), min(recent_close)
            p_mid = (p_high + p_low) / 2 if (p_high + p_low) > 0 else 1.0
            p_range = (p_high - p_low) / p_mid
            if p_range < PRE_BREAKOUT_ACCUM_PRICE_RANGE:
                pattern = "ACCUMULATION"
                # Score: volume acceleration strength + how flat the price is
                vol_growth = vol_vals[-1] / vol_vals[0] if vol_vals[0] > 0 else 1.0
                score = 30 + min(30, vol_growth * 10) + max(0, (1.0 - p_range / PRE_BREAKOUT_ACCUM_PRICE_RANGE) * 20)

    # ── Pattern 2: SQUEEZE ────────────────────────────────────
    # ATR at N-candle low + price above EMA21 (uptrend compression)
    if pattern is None and above_ema21:
        lookback = min(PRE_BREAKOUT_SQUEEZE_LOOKBACK, len(df) - 5)
        if lookback >= 10:
            # Compute rolling ATR for comparison
            tr = pd.concat([
                high - low,
                (high - close.shift(1)).abs(),
                (low  - close.shift(1)).abs(),
            ], axis=1).max(axis=1)
            atr_series = tr.ewm(alpha=1.0 / 14, adjust=False).mean()
            recent_atrs = atr_series.iloc[-lookback:]
            current_atr = float(atr_series.iloc[-1])
            min_atr     = float(recent_atrs.min())
            # Current ATR within 10% of the lookback minimum = squeeze
            if current_atr > 0 and current_atr <= min_atr * 1.10:
                pattern = "SQUEEZE"
                # Score: how tight the squeeze is + uptrend strength
                ema_dist = (price_now / float(ema21.iloc[-1]) - 1)
                score = 35 + min(20, ema_dist * 500) + min(25, (1.0 - current_atr / float(recent_atrs.mean())) * 50)

    # ── Pattern 3: BASE_SPRING ────────────────────────────────
    # Support tested multiple times with declining red-candle volume
    if pattern is None:
        lookback = 30
        if len(df) >= lookback:
            recent = df.iloc[-lookback:]
            # Find approximate support level — lowest low tested multiple times
            lows_window = recent["low"].values
            # Cluster lows within 0.5% of each other
            support_level = float(min(lows_window))
            tolerance     = support_level * 0.005
            # Count candles that touched within tolerance of support
            touches = []
            for i, l in enumerate(lows_window):
                if abs(float(l) - support_level) <= tolerance:
                    touches.append(i)

            if len(touches) >= PRE_BREAKOUT_BASE_TESTS:
                # Check red candle volume is declining across touches
                red_vols_at_touches = []
                for idx in touches:
                    c = float(recent["close"].iloc[idx])
                    o = float(recent["open"].iloc[idx])
                    if c < o:  # red candle at support
                        red_vols_at_touches.append(float(recent["volume"].iloc[idx]))
                if len(red_vols_at_touches) >= 2:
                    # Volume declining? At least last touch has less vol than first
                    if red_vols_at_touches[-1] < red_vols_at_touches[0] * 0.8:
                        # Current price should be bouncing off support, not sitting on it
                        if price_now > support_level * 1.005:
                            pattern = "BASE_SPRING"
                            vol_decline = 1.0 - (red_vols_at_touches[-1] / red_vols_at_touches[0])
                            score = 30 + len(touches) * 5 + min(25, vol_decline * 40)

    if pattern is None:
        return None

    score = round(min(score, 100), 2)

    log.debug(f"🔮 [PRE_BREAKOUT] {sym} {pattern} | score={score:.0f} | "
              f"RSI={rsi:.0f} | ATR={atr_pct*100:.2f}%")

    return {
        "symbol":       sym,
        "price":        price_now,
        "score":        score,
        "rsi":          round(rsi, 2),
        "atr_pct":      round(atr_pct, 6),
        "entry_signal": pattern,
        "vol_ratio":    round(float(volume.iloc[-1]) / float(volume.iloc[-20:-1].mean())
                              if float(volume.iloc[-20:-1].mean()) > 0 else 1.0, 2),
    }


def find_prebreakout_opportunity(tickers: pd.DataFrame, budget: float,
                                  exclude: set, open_symbols: set) -> dict | None:
    """
    Scan for pre-breakout setups: accumulation, squeeze, or base-spring patterns.
    Runs after moonshot burst scan — catches what moonshot can't see because
    no spike has happened yet.
    """
    df = tickers.copy()
    df = df[df["quoteVolume"] >= PRE_BREAKOUT_MIN_VOL]
    df = df[df["lastPrice"]   >= MIN_PRICE]
    df = df[~df["symbol"].isin(open_symbols | exclude | _api_blacklist)]
    # Filter out dead coins from liquidity blacklist
    now_ts = time.time()
    df = df[~df["symbol"].apply(lambda s: _liquidity_blacklist.get(s, 0) > now_ts)]
    # Focus on coins with moderate recent movement — not dead, not already pumped
    df = df[(df["priceChangePercent"].abs() >= 0.5) & (df["priceChangePercent"].abs() <= 10)]
    candidates = df.sort_values("quoteVolume", ascending=False).head(30)["symbol"].tolist()

    log.info(f"🔮 [PRE_BREAKOUT] Scanning {len(candidates)} candidates")
    if not candidates:
        return None

    # Pre-build vol lookup for dead coin check inside scorer
    ticker_vol_map = dict(zip(df["symbol"], df["quoteVolume"].fillna(0)))

    scored = []
    with ThreadPoolExecutor(max_workers=5) as ex:
        futures = {ex.submit(evaluate_prebreakout_candidate, sym): sym for sym in candidates}
        for f in as_completed(futures):
            try:
                result = f.result()
                if result and result["score"] >= 30:
                    # Dead coin check using 24h vol from ticker
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


# ── Scanner: Trinity ───────────────────────────────────────────

def evaluate_trinity_candidate(sym: str) -> dict | None:
    """
    Evaluate a single BTC/ETH/SOL symbol for a Trinity recovery entry.

    Conditions (ALL required):
    1. Price down ≥ TRINITY_DROP_PCT across ANY lookback window (4h or 8h)
       — institutional dips play out over hours, not minutes.
    2. RSI between TRINITY_MIN_RSI and TRINITY_MAX_RSI
       — widened: RSI 35-45 is already significantly oversold for these assets.
    3. Price stabilising — last candle green OR second-to-last green
       — allows entry one candle after the turn, not just on the exact bar.
    4. Volume recovery — entry candle vol ≥ TRINITY_VOL_BURST × avg
       — lowered: the turn itself is often quiet, the burst comes after.

    Returns opp dict with ATR-based TP/SL if all conditions pass, else None.
    """
    # 120 × 15m = 30h of data — enough for ATR(14) warmup + 8h drop check
    df = parse_klines(sym, interval="15m", limit=120, min_len=40)
    if df is None:
        return None

    close  = df["close"]
    volume = df["volume"]
    opens  = df["open"]

    price_now = float(close.iloc[-1])

    # ── 1. Multi-window drop check ────────────────────────────
    # Check across multiple lookback periods — use the deepest drop found.
    # This catches both sharp 4h crashes and gradual 8h selloffs.
    best_drop = 0.0
    for candles_back in TRINITY_DROP_LOOKBACK_CANDLES:
        if len(close) > candles_back + 1:
            price_then = float(close.iloc[-(candles_back + 1)])
            drop = (price_then - price_now) / price_then if price_then > 0 else 0.0
            best_drop = max(best_drop, drop)

    if best_drop < TRINITY_DROP_PCT:
        return None  # hasn't dropped enough in any window

    # ── 2. RSI filter ─────────────────────────────────────────
    rsi = calc_rsi(close)
    if np.isnan(rsi) or not (TRINITY_MIN_RSI <= rsi <= TRINITY_MAX_RSI):
        return None  # not in recovery zone

    # ── 3. Stabilising — recent green candle ──────────────────
    # Allow entry if EITHER the current or prior candle is green.
    # The exact bottom candle is often a doji or small red; the
    # confirmation green comes one bar later.
    curr_green = float(close.iloc[-1]) >= float(opens.iloc[-1])
    prev_green = float(close.iloc[-2]) >= float(opens.iloc[-2])
    if not (curr_green or prev_green):
        return None  # no stabilisation signal yet

    # ── 4. Volume recovery ────────────────────────────────────
    avg_vol   = float(volume.iloc[-21:-1].mean())
    curr_vol  = float(volume.iloc[-1])
    vol_burst = (curr_vol / avg_vol) if avg_vol > 0 else 1.0
    if vol_burst < TRINITY_VOL_BURST:
        return None  # no volume confirmation

    # ── ATR-based TP/SL ───────────────────────────────────────
    atr     = calc_atr(df, period=14)
    atr_pct = atr / price_now if price_now > 0 else 0.01

    tp_pct = max(TRINITY_TP_MIN, atr_pct * TRINITY_TP_ATR_MULT)
    sl_pct = min(TRINITY_SL_MAX, atr_pct * TRINITY_SL_ATR_MULT)
    # Ensure R:R is at least 1.5:1 — if SL too wide, skip
    if sl_pct > 0 and tp_pct / sl_pct < 1.5:
        tp_pct = sl_pct * 1.8  # enforce minimum R:R

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
    """
    Scan BTC/ETH/SOL for a Trinity recovery entry.
    Returns the first qualifying candidate in priority order (SOL > ETH > BTC).
    Max one Trinity trade at a time — enforced by the caller checking alt_trades.
    """
    # Skip if a Trinity trade is already open
    if any(t.get("label") == "TRINITY" for t in alt_trades):
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
        except Exception: body = e.response.text if e.response else "no response"
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
        except Exception: body = e.response.text if e.response else "no response"
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
    ema21_dist_pct = opp.get("ema21_dist_pct",  atr_pct * 1.5)
    avg_candle_pct = opp.get("avg_candle_pct",  atr_pct)
    signal         = opp.get("entry_signal",
                             classify_entry_signal(crossed_now=crossed_now,
                                                    vol_ratio=vol_ratio, rsi=rsi))

    # ── TP — driven by entry signal via lookup table ───────────
    tp_mult  = _SIGNAL_TP_MULT.get(signal, SCALPER_TP_MULT_DEFAULT)
    tp_label = f"{signal.lower()}×{tp_mult}"

    atr_tp      = atr_pct * tp_mult
    candle_cap  = avg_candle_pct * SCALPER_TP_CANDLE_MULT
    tp_pct      = min(atr_tp, candle_cap)             # whichever is more conservative
    # Fee-aware TP floor — dynamically computed from actual fee rates when available
    dynamic_tp_floor = calc_fee_aware_tp_floor()
    tp_pct      = min(SCALPER_TP_MAX, max(dynamic_tp_floor, tp_pct))

    if atr_tp > candle_cap:
        tp_label += f" (candle-capped {candle_cap*100:.1f}%)"

    # ── SL — driven by entry signal, with score-based override ──
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

    # For crossover entries, anchor SL to EMA21 distance — that's where
    # the thesis actually breaks. Use whichever is larger (EMA21 or ATR-based)
    # to avoid placing SL inside normal price oscillation.
    if signal == "CROSSOVER" and ema21_dist_pct > 0:
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
    hitting the SL costs exactly SCALPER_RISK_PER_TRADE of current balance,
    adjusted by a Kelly Lite score multiplier.

      base_risk  = balance × SCALPER_RISK_PER_TRADE × kelly_mult(score)
      budget     = base_risk / sl_pct

    Kelly Lite tiers (relative to SCALPER_THRESHOLD so they auto-adjust):
      score < threshold+15  → 0.60× (marginal — minimum conviction)
      score < threshold+30  → 0.80× (solid — clear signal)
      score < threshold+45  → 1.00× (standard — multi-signal)
      score ≥ threshold+45  → 1.20× (high confluence — already gets partial TP)

    Hard-capped at SCALPER_BUDGET_PCT regardless of multiplier.
    Returns (budget, tp_pct, sl_pct, tp_label, sl_label).
    Falls back to the percentage cap if dynamic TP/SL can't be computed.
    """
    score = opp.get("score", SCALPER_THRESHOLD)
    gap   = score - SCALPER_THRESHOLD  # how far above the entry bar
    if   gap < 15: kelly_mult = KELLY_MULT_MARGINAL
    elif gap < 30: kelly_mult = KELLY_MULT_SOLID
    elif gap < 45: kelly_mult = KELLY_MULT_STANDARD
    else:          kelly_mult = KELLY_MULT_HIGH_CONF

    try:
        tp_pct, sl_pct, tp_label, sl_label = calc_dynamic_tp_sl(opp)
        if sl_pct > 0:
            eff_budget_pct = get_effective_budget_pct("SCALPER")
            base_risk   = balance * SCALPER_RISK_PER_TRADE * kelly_mult
            risk_budget = base_risk / sl_pct
            capped      = min(risk_budget, balance * eff_budget_pct)
            log.debug(f"[SCALPER] Kelly mult {kelly_mult:.2f}× "
                      f"(score {score:.0f}, gap +{gap:.0f}) → ${capped:.2f}")
            return round(capped, 2), tp_pct, sl_pct, tp_label, sl_label
    except Exception:
        pass
    # Fallback — use pct cap and let open_position compute TP/SL itself
    return round(balance * get_effective_budget_pct("SCALPER"), 2), 0.0, 0.0, "", ""


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

    # 🟢 Spread + bid-depth check — reject pairs with wide spread OR thin books.
    # SCALPER: tight 0.4% spread. MOONSHOT: wider 0.8%.
    # Depth gate: sum all bids within DEPTH_PCT_RANGE (2%) of best bid.
    # If total bid USDT < position_value × DEPTH_BID_RATIO, our market sell
    # at SL would eat through the book and gap past the stop price.
    # Check is advisory — never blocks on error.
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

                # ── Bid depth sum gate ────────────────────────────
                # Sum the USDT value of all bids within DEPTH_PCT_RANGE of best_bid.
                # This catches wash-traded pairs that show a tight spread but have
                # almost no real liquidity behind it — our SL exit would gap straight
                # through a thin book and realise far worse than the SL price.
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

                # Note 4 — feed real spread back into dead-coin tracking.
                strategy_key = "SCALPER" if label in ("SCALPER", "TRINITY") else "MOONSHOT"
                check_dead_coin(symbol, 0.0, spread, strategy_key)
        except Exception:
            pass  # spread/depth check is advisory — don't block on error

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

    # ── KEY FIX: SCALPER + TRINITY get exchange TP limit order ──
    # MOONSHOT/REVERSAL: NO limit order — bot-monitored only.
    # TRINITY shares the scalper approach: deep liquidity on BTC/ETH/SOL means
    # exchange limit orders fill reliably with no slippage risk.
    if label in ("SCALPER", "TRINITY"):
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
        "entry_signal":   opp.get("entry_signal", "UNKNOWN"),
        "sentiment":      opp.get("sentiment"),
        # ATR-based trail width — set at entry from scorer, persisted across restarts.
        # check_exit uses this instead of the static SCALPER_TRAIL_PCT constant.
        "trail_pct":      opp.get("trail_pct", SCALPER_TRAIL_PCT) if label == "SCALPER" else None,
        # ATR% at entry — stored so check_exit can compute ATR-stepped trail tiers
        # without re-fetching klines. Defaults to trail_pct as a safe fallback.
        # Stored for ALL labels: Moonshot/Trinity use it for the wide-trail threshold.
        # Note: explicit None check — atr_pct=0.0 is falsy but valid.
        "atr_pct":        opp.get("atr_pct") if opp.get("atr_pct") is not None else (
                              opp.get("trail_pct", SCALPER_TRAIL_PCT) if label == "SCALPER"
                              else actual_sl * 0.5  # conservative proxy: half the SL width
                          ),
        # Move maturity at entry — logged at close for adaptive learning
        "move_maturity":  opp.get("move_maturity"),
        # High-confidence scalper trades get fast breakeven: SL moves to entry at +1.5%
        # Moonshot trades get breakeven at +4% — prevents giving back gains before partial TP
        # Trinity trades get breakeven at +1% — tight, liquid, small moves matter
        "breakeven_act":  (SCALPER_BREAKEVEN_ACT if (
                               label == "SCALPER" and
                               opp.get("score", 0) >= SCALPER_BREAKEVEN_SCORE
                           ) else MOONSHOT_BREAKEVEN_ACT if label == "MOONSHOT"
                           else TRINITY_BREAKEVEN_ACT if label == "TRINITY"
                           else None),
        "breakeven_done": False,   # flips True once SL has been moved to entry
        # ── Partial TP (MOONSHOT / REVERSAL / high-score SCALPER) ──
        # Moonshot has two stages: micro (30% at +2%) then main (50% at +10%).
        # Stage 1 (micro): sell 30%, SL → entry. Captures the consistent +2-3% pops.
        # Stage 2 (main):  sell 50% of remaining, trailing stop activates.
        # Note 11: high-score scalper trades sell 30% at the normal TP price;
        # the remaining 70% rides a wider 2×ATR trailing stop with no hard cap.
        "micro_tp_price": (
            round_price_to_tick(actual_entry * (1 + MOONSHOT_MICRO_TP_PCT), tick_size)
            if label == "MOONSHOT" else None
        ),
        "micro_tp_ratio":   MOONSHOT_MICRO_TP_RATIO if label == "MOONSHOT" else None,
        "micro_tp_hit":     False,
        "partial_tp_price": (
            tp_price  # SCALPER: partial fires at the same TP level already on the exchange
            if (label == "SCALPER" and opp.get("score", 0) >= SCALPER_PARTIAL_TP_SCORE) else
            round_price_to_tick(actual_entry * (1 + MOONSHOT_PARTIAL_TP_PCT), tick_size)
            if label == "MOONSHOT" else
            round_price_to_tick(actual_entry * (1 + REVERSAL_PARTIAL_TP_PCT), tick_size)
            if label == "REVERSAL" else None
        ),
        "partial_tp_ratio": (
            SCALPER_PARTIAL_TP_RATIO  if (label == "SCALPER" and opp.get("score", 0) >= SCALPER_PARTIAL_TP_SCORE) else
            MOONSHOT_PARTIAL_TP_RATIO if label == "MOONSHOT" else
            REVERSAL_PARTIAL_TP_RATIO if label == "REVERSAL" else None
        ),
        "partial_tp_hit":   False,   # flips True once stage 2 fires
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

    keltner_line = (f"Keltner:     ✅ breakout confirmed (+{opp.get('keltner_bonus',0):.0f}pts)\n"
                    if opp.get("keltner_bonus") else "")

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
    micro_tp_line   = ""
    if trade.get("micro_tp_price") and label == "MOONSHOT":
        micro_ratio_pct = (trade["micro_tp_ratio"] or 0.3) * 100
        micro_pct       = (trade["micro_tp_price"] / actual_entry - 1) * 100
        micro_tp_line   = (f"Micro TP:    {micro_ratio_pct:.0f}% @ "
                           f"<b>${trade['micro_tp_price']:.6f}</b>"
                           f"  (+{micro_pct:.1f}%) → SL → entry 🔒\n")
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
    elif trade.get("partial_tp_price") and label == "SCALPER":
        # Note 11 — high-score scalper partial TP
        ratio_pct   = (trade["partial_tp_ratio"] or 0.3) * 100
        partial_pct = (trade["partial_tp_price"] / actual_entry - 1) * 100
        trail_wide  = round(opp.get("atr_pct", SCALPER_TRAIL_PCT) * SCALPER_PARTIAL_TP_TRAIL_MULT * 100, 1)
        partial_tp_line = (f"Partial TP:  {ratio_pct:.0f}% @ "
                           f"<b>${trade['partial_tp_price']:.6f}</b>"
                           f"  (+{partial_pct:.1f}%) → {trail_wide}% ATR trail (no cap)\n")

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
        f"{keltner_line}"
        f"{tp_display}"
        f"{sl_display}"
        f"{micro_tp_line}"
        f"{partial_tp_line}"
        f"{breakeven_line}"
        f"{timeout_line}"
        f"{tp_status}\n"
        f"Score: {opp.get('score',0)} | Signal: {opp.get('entry_signal','?')}"
        + (f" 🔥 (confluence +{opp.get('confluence_bonus',0):.0f})" if opp.get('confluence_bonus') else "")
        + (f" 📐 (keltner +{opp.get('keltner_bonus',0):.0f})" if opp.get('keltner_bonus') else "")
        + f" | RSI: {opp.get('rsi','?')} ({opp.get('rsi_delta',0):+.1f}) | Vol: {opp.get('vol_ratio','?')}x"
        + (f" | Trail: {opp.get('trail_pct', SCALPER_TRAIL_PCT)*100:.1f}%" if label == "SCALPER" else "")
        + (f" | Kelly: {opp.get('kelly_mult', 1.0):.2f}×" if label == "SCALPER" and opp.get("kelly_mult") else "")
        + (f"\nMaturity: {opp.get('move_maturity',0):.0%}" + (f" (-{opp.get('maturity_penalty',0):.0f}pts)" if opp.get('maturity_penalty',0) > 0 else "") if opp.get('move_maturity') is not None else "")
        + (f" | Threshold: {get_effective_threshold(label):.0f}" if _adaptive_offsets.get(label, 0) != 0 else "")
    )
    save_state()
    return trade


def check_exit(trade, best_score: float = 0) -> tuple[bool, str]:
    symbol      = trade["symbol"]
    label       = trade["label"]
    tp_order_id = trade.get("tp_order_id")

    # held_min computed once here — used by timeout checks, graduated exits,
    # flat exit, vol collapse, and trailing stop logic below.
    # Guard: fromisoformat on old state may return a naive datetime (no tz info).
    # Normalize to UTC-aware before subtracting to avoid TypeError.
    try:
        opened = datetime.fromisoformat(trade["opened_at"])
        if opened.tzinfo is None:
            opened = opened.replace(tzinfo=timezone.utc)
        held_min = (datetime.now(timezone.utc) - opened).total_seconds() / 60
    except Exception:
        held_min = 0.0

    # ── Timeout logic ─────────────────────────────────────────
    # MOONSHOT: graduated — timeout depends on how the trade is performing.
    #   Flat trade gets cut early; a trade that's working gets more time.
    # REVERSAL: hard 2h ceiling (short-hold strategy, no accommodation).
    # SCALPER: no max_hours (uses trailing stop / flat exit instead).
    if trade.get("max_hours"):
        if label == "MOONSHOT":
            # Once partial TP has fired the trade is risk-free — let the trailing
            # stop run it. Only apply the hard timeout to trades still in stage 1.
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

    # ── Micro TP (MOONSHOT stage 1 — sell 30% at +2%) ───────────
    # Fires before the main partial TP. Captures the consistent +2-3% pops
    # that moonshots produce before reversing. Moves SL to entry (risk-free).
    if (label == "MOONSHOT"
            and not trade.get("micro_tp_hit")
            and trade.get("micro_tp_price")
            and price >= trade["micro_tp_price"]):
        log.info(f"🎯μ [{label}] Micro TP: {symbol} | {pct:+.2f}%")
        return True, "MICRO_TP"

    # ── Partial TP (MOONSHOT stage 2 / REVERSAL) ──────────────
    # MOONSHOT: fires at +10% AFTER micro has already taken 30%.
    # REVERSAL: fires at +2.5% (no micro stage).
    # After this, execute_partial_tp() sells half of remaining, trailing stop activates.
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
        # ── Note 11 — High-score partial TP ───────────────────
        # For score ≥ SCALPER_PARTIAL_TP_SCORE, the exchange TP limit order sells
        # 30% when price hits tp_price.  We detect the fill the same way as a normal
        # TAKE_PROFIT (limit order disappears) but instead of closing, we:
        #   • mark partial_tp_hit = True
        #   • move SL to entry (risk-free remainder)
        #   • widen trail to 2×ATR — no hard cap
        if (trade.get("partial_tp_price")
                and not trade.get("partial_tp_hit")
                and price >= trade["partial_tp_price"]):
            # Check if the exchange TP limit has been (partially) filled.
            # For paper trade or if no order, trigger immediately on price.
            if PAPER_TRADE or not tp_order_id or tp_order_id not in get_open_order_ids(symbol):
                log.info(f"🎯½ [SCALPER] Partial TP triggered: {symbol} | {pct:+.2f}%")
                return True, "PARTIAL_TP"

        # ── TP: limit order check (normal full close, post-partial path) ─
        # Only poll get_open_order_ids when price is within 2% of TP — avoids
        # an unnecessary API call every 2s when the trade is far from target.
        # The 0.995 fill-confirm threshold below already filters noise.
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

        # ── Note 2 — ATR-stepped trailing stop ────────────────
        # Entry ATR stored in trade["atr_pct"]; fall back to trail_pct if missing
        # (handles trades opened before this upgrade).
        atr_pct   = trade.get("atr_pct") or trade.get("trail_pct") or SCALPER_TRAIL_PCT
        # Use highest_price for tier determination — the tier should be based on the
        # peak the trade reached, not the current (potentially pulled-back) price.
        # A trade that ran +10% and pulled back to +6.7% should still be on the wide tier2
        # trail, not snap back to the tight tier1 trail mid-move.
        peak_profit = (trade["highest_price"] / trade["entry_price"] - 1)
        profit_pct  = (price / trade["entry_price"] - 1)  # used for post-partial check only

        # Tier 2: peak has run ≥ SCALPER_TRAIL_TIER2_THRESH × ATR — widen trail
        # to give parabolic moves room.  Tier 2 overrides tier 1 when active.
        if peak_profit >= atr_pct * SCALPER_TRAIL_TIER2_THRESH:
            active_trail = atr_pct * SCALPER_TRAIL_ATR_TIER2
            tier_label   = f"tier2 {active_trail*100:.1f}%"
        # Tier 1: peak has run ≥ SCALPER_TRAIL_ATR_ACTIVATE × ATR — activate trail
        elif peak_profit >= atr_pct * SCALPER_TRAIL_ATR_ACTIVATE:
            active_trail = atr_pct * SCALPER_TRAIL_ATR_TIER1
            tier_label   = f"tier1 {active_trail*100:.1f}%"
        else:
            active_trail = None  # below activation threshold — no ATR trail yet
            tier_label   = ""

        # After partial TP the remainder uses the wider 2×ATR trail regardless of tier
        if trade.get("partial_tp_hit"):
            active_trail = atr_pct * SCALPER_PARTIAL_TP_TRAIL_MULT
            tier_label   = f"post-partial {active_trail*100:.1f}%"

        # Also honour the legacy fixed-pct trail as a minimum floor when ATR trail
        # is active — ensures we never widen beyond what the user originally tuned.
        if active_trail is not None:
            # Clamp: never narrower than tier-1 floor, never wider than tier-2 ceiling
            active_trail = min(SCALPER_TRAIL_MAX,
                               max(SCALPER_TRAIL_MIN, active_trail))
            if price <= trade["highest_price"] * (1 - active_trail):
                log.info(f"📉 [{label}] ATR trail stop ({tier_label}): {symbol} | {pct:+.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "TRAILING_STOP"
        else:
            # Below ATR activation — fall back to the original static trail if it was
            # already active (i.e. trade crossed +SCALPER_TRAIL_ACT before ATR logic
            # existed).  Keeps backward-compat for bot restarts mid-trade.
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
            if (best_score - trade.get("score", 0)) >= SCALPER_ROTATE_GAP:
                log.info(f"🔀 [{label}] Rotation: {symbol} | {pct:+.2f}%")
                if not PAPER_TRADE and tp_order_id:
                    cancel_order(symbol, tp_order_id, label)
                return True, "ROTATION"

    elif label == "MOONSHOT" and trade.get("partial_tp_hit"):
        # After partial TP: trailing stop on remainder — no fixed target, ride the move.
        # Note 2: widen trail to MOONSHOT_TRAIL_ATR_WIDE if profit ≥ 4×ATR.
        atr_pct     = trade.get("atr_pct") or MOONSHOT_SL * 0.5  # rough proxy if not stored
        peak_profit = (trade["highest_price"] / trade["entry_price"] - 1)
        profit_pct  = (price / trade["entry_price"] - 1)
        trail_pct   = (MOONSHOT_TRAIL_ATR_WIDE
                       if peak_profit >= atr_pct * MOONSHOT_TRAIL_WIDE_THRESH
                       else MOONSHOT_TRAIL_PCT)
        trail_sl   = trade["highest_price"] * (1 - trail_pct)
        if price <= trail_sl:
            log.info(f"📉 [{label}] Trail stop ({trail_pct*100:.0f}%): {symbol} | {pct:+.2f}% | "
                     f"high {((trade['highest_price']/trade['entry_price'])-1)*100:.1f}%")
            return True, "TRAILING_STOP"

    else:
        # MOONSHOT (pre-partial) / REVERSAL: fixed TP price check
        if price >= trade["tp_price"]:
            log.info(f"🎯 [{label}] TP: {symbol} | +{pct:.2f}%")
            return True, "TAKE_PROFIT"

    # ── MOONSHOT-specific exits ───────────────────────────────
    if label == "MOONSHOT":
        # After micro or partial TP, trade is risk-free (SL at entry) — let trailing
        # stop handle it. Only apply timeouts to trades still carrying risk.
        _risk_free = trade.get("micro_tp_hit") or trade.get("partial_tp_hit")

        # Graduated timeout — give winning trades more time
        # Flat timeout: only fires near breakeven (-1% to +0.5%).
        # If deeply negative, the SL handles it — don't pre-empt a potential recovery.
        if not _risk_free and -1.0 <= pct < 0.5 and held_min >= MOONSHOT_TIMEOUT_FLAT_MINS:
            log.info(f"😴 [{label}] Flat timeout: {symbol} | {pct:+.2f}% after {held_min:.0f}min")
            return True, "TIMEOUT"
        if not _risk_free and pct < 5.0 and held_min >= MOONSHOT_TIMEOUT_MARGINAL_MINS:
            log.info(f"⏰ [{label}] Marginal timeout: {symbol} | {pct:+.2f}% after {held_min:.0f}min")
            return True, "TIMEOUT"

        # Mid-hold momentum decay — pump is over if volume declining AND price flat.
        # Replaces the old single-candle VOL_COLLAPSE ratio check which was too
        # aggressive on normal consolidation patterns. The decay detector requires
        # N consecutive declining-volume candles with flat price — a much stronger signal.
        if not _risk_free and held_min >= MOMENTUM_DECAY_MIN_HELD and pct < 5.0:
            if detect_momentum_decay(symbol):
                log.info(f"📉 [{label}] Momentum decay: {symbol} | {pct:+.2f}%")
                return True, "VOL_COLLAPSE"

    # ── REVERSAL-specific exits ───────────────────────────────
    if label == "REVERSAL" and not trade.get("partial_tp_hit"):
        # Mean-reversion shelf-life check.
        # If the bounce hasn't made REVERSAL_FLAT_PROGRESS (40%) of the way
        # from entry to TP within REVERSAL_FLAT_MINS (45min), the thesis is
        # stale — the oversold condition has resolved without our coin bouncing.
        # Exit now at a small loss / breakeven rather than waiting for the hard
        # 2h timeout with a larger loss, or sitting in dead capital.
        # Guards:
        #   - Only fires before partial TP hits (remainder is risk-free by then)
        #   - Only fires when price is above entry — if already at a loss, the
        #     SL handles it; this exit is for "stuck but not losing" situations
        #   - Only fires when TP range is positive (avoids divide-by-zero)
        if held_min >= REVERSAL_FLAT_MINS and pct >= 0:
            tp_range = trade["tp_price"] - trade["entry_price"]
            if tp_range > 0:
                progress = (price - trade["entry_price"]) / tp_range
                if progress < REVERSAL_FLAT_PROGRESS:
                    log.info(f"😴 [{label}] Flat-progress exit: {symbol} | "
                             f"{pct:+.2f}% | progress {progress*100:.0f}% "
                             f"< {REVERSAL_FLAT_PROGRESS*100:.0f}% after {held_min:.0f}min")
                    return True, "FLAT_EXIT"

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

    log.info(f"👀 [{label}] {symbol} | {pct:+.2f}% | {held_min:.0f}min | "
             f"High: {((trade['highest_price']/trade['entry_price'])-1)*100:.2f}%")
    return False, ""


def execute_partial_tp(trade, micro: bool = False) -> bool:
    """
    Sell a portion of the position at market price.
    Mutates the trade dict in place — the trade stays live with reduced qty.

    Two modes:
      micro=True  — Moonshot stage 1: sell 30% at +2%, SL → entry.
      micro=False — Normal partial TP: sell 50% at +10% (Moonshot) or +2.5% (Reversal).

    After firing:
      - qty/budget_used reduced proportionally
      - sl_price → entry_price (remainder is risk-free)
      - micro_tp_hit or partial_tp_hit set to True
      - A partial P&L entry is appended to trade_history

    Returns True if partial sell succeeded, False if it failed hard.
    """
    label   = trade["label"]
    symbol  = trade["symbol"]
    ratio   = (trade.get("micro_tp_ratio", MOONSHOT_MICRO_TP_RATIO) if micro
               else trade.get("partial_tp_ratio", 0.5))
    reason_tag = "MICRO_TP" if micro else "PARTIAL_TP"

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
        log.warning(f"[{label}] {reason_tag} skipped — qty too small "
                    f"(partial={partial_qty}, remaining={remaining_qty}, min={min_qty})")
        # Skip this stage so we don't retry
        if micro:
            trade["micro_tp_hit"] = True
        else:
            trade["partial_tp_hit"] = True
        return True

    partial_sell_id  = None
    partial_sold_at_ms = int(time.time() * 1000)  # record before sell for fill query
    if not PAPER_TRADE:
        # ── For SCALPER: cancel the full-qty TP limit before selling partial ──
        # The limit order was placed for 100% of qty. After selling partial_qty at
        # market we only hold remaining_qty, so the old limit would over-sell.
        # Cancel it now; re-place for remaining_qty after the partial fill.
        if label == "SCALPER" and trade.get("tp_order_id"):
            cancel_order(symbol, trade["tp_order_id"], label)
            trade["tp_order_id"] = None

        try:
            result = private_post("/api/v3/order", {
                "symbol": symbol, "side": "SELL",
                "type": "MARKET", "quantity": str(partial_qty),
            })
            partial_sell_id = result.get("orderId")
            log.info(f"✅ [{label}] Partial sell: {partial_qty} {symbol} → {result}")
        except requests.exceptions.HTTPError as e:
            try:    body = e.response.json()
            except Exception: body = {"msg": str(e)}
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
    except Exception:
        ticker_price = (trade.get("micro_tp_price") if micro
                        else trade.get("partial_tp_price", trade["entry_price"]))

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
        "exit_reason":   reason_tag,
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
    if micro:
        trade["micro_tp_hit"]  = True
    else:
        trade["partial_tp_hit"]= True
    # close_position uses this as bought_at_ms so fill query only sees remaining fills
    trade["bought_at_ms"]      = partial_sold_at_ms

    # ── SCALPER: re-place TP limit for remaining qty ──────────────────
    # The original limit was cancelled above. Place a new one at the same
    # tp_price but sized for remaining_qty — exchange now monitors the tail.
    if label == "SCALPER" and not PAPER_TRADE and remaining_qty > 0:
        _, _, _, tick_size = get_symbol_rules(symbol)
        new_tp_id = place_limit_sell(symbol, remaining_qty, trade["tp_price"],
                                     label, tag="TP_REMAINDER")
        trade["tp_order_id"] = new_tp_id
        if new_tp_id:
            log.info(f"[SCALPER] Re-placed TP limit for {remaining_qty} @ ${trade['tp_price']:.6f}")
        else:
            log.warning(f"[SCALPER] TP re-place failed for {symbol} — remainder monitored by bot")

    # Save immediately after mutation — minimises the crash window between
    # "sell confirmed on exchange" and "state reflects reduced position"
    save_state()

    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    fills_note= "✅ actual fills" if partial_fills.get("avg_sell_price") else "⚠️ estimated"
    icon      = "🎯μ" if micro else {"MOONSHOT":"🌙","REVERSAL":"🔄"}.get(label, "🎯")
    stage_str = "Micro TP" if micro else "Partial TP"

    log.info(f"{icon} [{label}] {stage_str} {symbol}: sold {partial_qty} @ ${actual_exit:.6f} "
             f"P&L ${partial_pnl:+.4f} ({partial_pct:+.2f}%) | "
             f"Remaining: {remaining_qty} @ SL entry")
    telegram(
        f"{icon} <b>{stage_str} — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:      <b>{symbol}</b>\n"
        f"Sold:      {partial_qty} ({ratio*100:.0f}%) @ <b>${actual_exit:.6f}</b>  [{fills_note}]\n"
        f"P&L:       <b>{partial_pct:+.2f}%  (${partial_pnl:+.2f})</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Remaining: {remaining_qty} still open\n"
        f"SL moved:  entry ${trade['entry_price']:.6f} (risk-free 🔒)\n"
        + (f"Next:      partial TP at +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}%"
           if micro and label == "MOONSHOT" else
           f"Trail:     {MOONSHOT_TRAIL_PCT*100:.0f}% below highest price (uncapped)"
           if label == "MOONSHOT" else
           f"Target:    ${trade['tp_price']:.6f}  (+{trade['tp_pct']*100:.0f}%)")
    )
    return True


def close_position(trade, reason) -> bool:
    label  = trade["label"]
    symbol = trade["symbol"]

    # For MOONSHOT/REVERSAL: market sell on ALL exits including TAKE_PROFIT
    # For SCALPER/TRINITY: TAKE_PROFIT is handled by exchange limit, others need market sell
    needs_sell = (
        (label in ("MOONSHOT", "REVERSAL")) or
        (label == "SCALPER" and reason in ("STOP_LOSS","TRAILING_STOP","TIMEOUT","FLAT_EXIT","ROTATION","VOL_COLLAPSE")) or
        (label == "TRINITY" and reason in ("STOP_LOSS","TIMEOUT"))
    )

    sell_order_id = None
    if needs_sell and not PAPER_TRADE:
        tp_order_id = trade.get("tp_order_id")
        if label in ("SCALPER", "TRINITY") and tp_order_id:
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
            except Exception: body = {"msg": e.response.text if e.response else "no response"}

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

        retries    = 5 if (reason == "TAKE_PROFIT" and label in ("SCALPER", "TRINITY")) else 3
        exit_fills = get_actual_fills(
            symbol, since_ms=bought_at_ms, retries=retries,
            buy_order_id=buy_order_id,
            sell_order_ids=known_sell_ids or None,
        )

    # Fallback ticker price if fills unavailable
    try:
        ticker_price = float(public_get("/api/v3/ticker/price", {"symbol": symbol})["price"])
    except Exception:
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

    # ── Giveback tracking — how much peak profit was returned ──────
    peak_price    = trade.get("highest_price", actual_entry)
    peak_profit   = (peak_price / actual_entry - 1) if actual_entry > 0 else 0.0
    actual_profit = (actual_exit / actual_entry - 1) if actual_entry > 0 else 0.0
    giveback_ratio = (
        (peak_profit - actual_profit) / peak_profit
        if peak_profit > 0.001 else 0.0  # only meaningful if trade went positive
    )

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
        # ── Adaptive learning fields ──
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

    # Track consecutive scalper losses for the streak circuit breaker
    global _consecutive_losses, _win_rate_pause_until
    if label == "SCALPER":
        if pnl_pct <= 0:
            _consecutive_losses += 1
        else:
            _consecutive_losses = 0   # any win resets the streak

    # ── Adaptive learning — update thresholds + rebalance budgets ──
    # These run on every close so the bot continuously adjusts to market conditions.
    try:
        update_adaptive_thresholds()
        rebalance_budgets()
    except Exception as e:
        log.debug(f"Adaptive learning update failed: {e}")

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
        "MICRO_TP":      ("🎯μ","Micro Take Profit"),
    }
    emoji, reason_label = icons.get(reason, ("✅", reason))

    fee_line   = f"Fees:    ${fee_usdt:.4f}\n" if fee_usdt > 0 else ""
    fills_note = "✅ actual fills" if exit_fills.get("avg_sell_price") else "⚠️ estimated"
    signal_str = trade.get("entry_signal", "")
    peak_line  = (f"Peak:    +{peak_profit*100:.1f}% (gave back {giveback_ratio*100:.0f}%)\n"
                  if peak_profit > 0.005 else "")

    telegram(
        f"{emoji} <b>{reason_label} — {label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:    <b>{symbol}</b>"
        + (f"  [{signal_str}]" if signal_str else "") + "\n"
        f"Entry:   ${actual_entry:.6f}\n"
        f"Exit:    <b>${actual_exit:.6f}</b>  [{fills_note}]\n"
        f"P&L:     <b>{pnl_pct:+.2f}%  (${pnl_usdt:+.2f})</b>\n"
        f"{peak_line}"
        f"{fee_line}"
        f"━━━━━━━━━━━━━━━\n"
        f"Session: {len(full_trades)} trades | Win: {win_rate:.0f}% | P&L: ${total_pnl:+.2f}"
    )
    log.info(f"📈 Closed {symbol} [{reason}] {pnl_pct:+.2f}% | Win:{win_rate:.0f}% P&L:${total_pnl:+.2f}")
    save_state()
    return True

# ── Heartbeat ─────────────────────────────────────────────────

def _trade_price_pct(trade: dict) -> tuple[float | None, float | None]:
    """
    Return (current_price, pct_from_entry) for an open trade.
    Uses WS price first, falls back to REST. Returns (None, None) on error.
    Centralises the repeated ws_price-or-REST pattern used in status/heartbeat.
    """
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

    scalper_lines = []
    for t in scalper_trades:
        _, pct = _trade_price_pct(t)
        if pct is not None:
            scalper_lines.append(f"  🟢 {t['symbol']} {pct:+.2f}%")
        else:
            scalper_lines.append(f"  🟢 {t['symbol']}")
    if not scalper_trades:
        if last_top_scalper:
            scalper_lines.append(f"  Watching: {last_top_scalper['symbol']} (score {last_top_scalper['score']})")
        else:
            scalper_lines.append("  Scanning...")

    alt_lines = []
    for t in alt_trades:
        _, pct = _trade_price_pct(t)
        if pct is not None:
            alt_lines.append(f"  {t['label']}: <b>{t['symbol']}</b> {pct:+.2f}%")
        else:
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
    Uses a single batch price fetch instead of one call per asset.
    """
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

        # Single batch fetch — /api/v3/ticker/price with no symbol returns all pairs
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
            lines.append(f"{t['label']}: <b>{t['symbol']}</b> | {pct:+.2f}% | "
                         f"TP: ${t['tp_price']:.6f} | SL: ${t['sl_price']:.6f}")
        else:
            lines.append(f"{t['label']}: {t['symbol']} (unavailable)")
    if not alt_trades:
        lines.append("Alt: scanning...")
    lines.append(f"Balance: <b>${balance:.2f} USDT</b>")
    telegram("\n".join(lines))


def _compute_metrics(trades: list) -> dict:
    """
    Compute trading performance metrics from trade_history.
    Excludes partial TP entries — they always show positive and skew all stats.

    Returns a dict with keys:
      total, wins, losses, win_rate, avg_win, avg_loss, profit_factor,
      total_pnl, max_drawdown, sharpe, best, worst,
      by_label: {SCALPER: {...}, MOONSHOT: {...}, REVERSAL: {...}},
      by_reason: {exit_reason: count}
    """
    full = [t for t in trades if not t.get("is_partial")]
    if not full:
        return {}

    pnls      = [t["pnl_pct"] for t in full]
    pnls_usdt = [t["pnl_usdt"] for t in full]
    wins      = [p for p in pnls if p > 0]
    losses    = [p for p in pnls if p <= 0]

    # Max drawdown from running equity curve
    equity   = 0.0
    peak     = 0.0
    max_dd   = 0.0
    for p in pnls_usdt:
        equity += p
        peak    = max(peak, equity)
        dd      = peak - equity
        max_dd  = max(max_dd, dd)

    # Trade-level Sharpe: mean / std * sqrt(n) — directional, not time-series
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

    # Per-strategy breakdown
    by_label = {}
    for lbl in ("SCALPER", "MOONSHOT", "REVERSAL", "TRINITY"):
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

    # Exit reason breakdown (full trades only)
    by_reason: dict = {}
    for t in full:
        r = t.get("exit_reason", "UNKNOWN")
        by_reason[r] = by_reason.get(r, 0) + 1

    # ── Giveback stats — how much peak profit is being returned ──
    givebacks = [t.get("giveback_ratio", 0) for t in full
                 if t.get("giveback_ratio") is not None and t.get("peak_profit_pct", 0) > 0.5]
    avg_giveback = sum(givebacks) / len(givebacks) if givebacks else None

    # ── Move maturity stats — are we entering too late? ──
    maturities = [t.get("move_maturity", 0) for t in full
                  if t.get("move_maturity") is not None]
    avg_maturity = sum(maturities) / len(maturities) if maturities else None

    # ── Per-signal performance breakdown ─────────────────────────
    by_signal = _compute_signal_stats(full)

    return {
        "total":         n,
        "wins":          len(wins),
        "losses":        len(losses),
        "win_rate":      len(wins) / n * 100,
        "avg_win":       sum(wins)  / len(wins)  if wins   else 0.0,
        "avg_loss":      sum(losses)/ len(losses) if losses else 0.0,
        "profit_factor": profit_factor,
        "total_pnl":     sum(pnls_usdt),
        "max_drawdown":  max_dd,
        "sharpe":        sharpe,
        "best":          best,
        "worst":         worst,
        "by_label":      by_label,
        "by_reason":     by_reason,
        "by_signal":     by_signal,
        "avg_giveback":  avg_giveback,
        "avg_maturity":  avg_maturity,
    }


def _cmd_metrics(balance: float):
    """Send a full performance metrics summary via Telegram."""
    full = [t for t in trade_history if not t.get("is_partial")]
    if not full:
        telegram("📊 <b>Metrics</b>\n━━━━━━━━━━━━━━━\nNo completed trades yet.")
        return

    m = _compute_metrics(trade_history)

    # ── Overall summary ──────────────────────────────────────
    pf_str = f"{m['profit_factor']:.2f}" if not math.isinf(m["profit_factor"]) else "∞"
    lines  = [
        f"📊 <b>Performance Metrics</b>",
        f"━━━━━━━━━━━━━━━",
        f"Trades:   <b>{m['total']}</b>  ({m['wins']}W / {m['losses']}L)",
        f"Win rate: <b>{m['win_rate']:.1f}%</b>",
        f"Avg win:  <b>+{m['avg_win']:.2f}%</b>  |  Avg loss: <b>{m['avg_loss']:.2f}%</b>",
        f"P-factor: <b>{pf_str}</b>  |  Sharpe: <b>{m['sharpe']:.2f}</b>",
        f"Total P&L:<b>${m['total_pnl']:+.2f}</b>  |  Max DD: <b>-${m['max_drawdown']:.2f}</b>",
        f"Balance:  <b>${balance:.2f}</b>",
    ]

    # ── Per-strategy ─────────────────────────────────────────
    icons = {"SCALPER": "🟢", "MOONSHOT": "🌙", "REVERSAL": "🔄"}
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

    # ── Exit reasons ─────────────────────────────────────────
    if m["by_reason"]:
        lines.append("━━━━━━━━━━━━━━━")
        reason_parts = [f"{r}: {c}" for r, c in
                        sorted(m["by_reason"].items(), key=lambda x: -x[1])]
        lines.append("Exits: " + "  ".join(reason_parts))

    # ── Per-signal performance ────────────────────────────────
    if m.get("by_signal"):
        sig_parts = []
        for sig, s in sorted(m["by_signal"].items(),
                              key=lambda x: -x[1]["total"]):
            if s["total"] < 2:
                continue
            emoji = "✅" if s["win_rate"] >= 50 else "⚠️" if s["win_rate"] >= 30 else "🔴"
            sig_parts.append(f"{emoji}{sig}: {s['total']}t "
                             f"{s['win_rate']:.0f}%WR "
                             f"avg {s['avg_pnl']:+.1f}%")
        if sig_parts:
            lines.append("━━━━━━━━━━━━━━━")
            lines.append("Signals:")
            for sp in sig_parts:
                lines.append(f"  {sp}")

    # ── Best / worst ─────────────────────────────────────────
    best  = m["best"]
    worst = m["worst"]
    lines.append("━━━━━━━━━━━━━━━")
    lines.append(f"Best:  {best['symbol']} {best['pnl_pct']:+.2f}% "
                 f"({best.get('exit_reason','?')})")
    lines.append(f"Worst: {worst['symbol']} {worst['pnl_pct']:+.2f}% "
                 f"({worst.get('exit_reason','?')})")

    # ── Adaptive learning stats ──────────────────────────────
    adaptive_lines = []
    if m.get("avg_giveback") is not None:
        gb = m["avg_giveback"]
        gb_status = ("✅ optimal" if GIVEBACK_TARGET_LOW <= gb <= GIVEBACK_TARGET_HIGH
                     else "⚠️ trail too wide" if gb > GIVEBACK_TARGET_HIGH
                     else "⚠️ trail too tight")
        adaptive_lines.append(f"Giveback: {gb*100:.0f}% avg ({gb_status})")
    if m.get("avg_maturity") is not None:
        mat = m["avg_maturity"]
        mat_status = ("✅ early entries" if mat < 0.6
                      else "⚠️ mid-move entries" if mat < 0.8
                      else "🔴 late entries")
        adaptive_lines.append(f"Maturity: {mat*100:.0f}% avg ({mat_status})")
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
    # Dead coin blacklist summary
    now_ts      = time.time()
    dead_active = sum(1 for v in _liquidity_blacklist.values() if v > now_ts)
    dead_pending= sum(1 for v in _liquidity_fail_count.values() if v > 0)

    telegram(
        f"⚙️ <b>Current Config</b>\n━━━━━━━━━━━━━━━\n"
        f"🟢 <b>Scalper</b>\n"
        f"  Max: {SCALPER_MAX_TRADES} × {get_effective_budget_pct('SCALPER')*100:.0f}% cap | 1% risk/trade\n"
        f"  TP: dynamic {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% (signal-aware, candle-capped)\n"
        f"  SL: dynamic {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}% (noise-floored)\n"
        f"  Trail: ATR-stepped\n"
        f"    Tier 1 (+{SCALPER_TRAIL_ATR_ACTIVATE:.0f}×ATR): trail {SCALPER_TRAIL_ATR_TIER1:.0f}×ATR behind high\n"
        f"    Tier 2 (+{SCALPER_TRAIL_TIER2_THRESH:.0f}×ATR): trail {SCALPER_TRAIL_ATR_TIER2:.0f}×ATR (wider on runners)\n"
        f"  Breakeven: score ≥{SCALPER_BREAKEVEN_SCORE} → lock at +{SCALPER_BREAKEVEN_ACT*100:.1f}%\n"
        f"  Partial TP: score ≥{SCALPER_PARTIAL_TP_SCORE} → sell {SCALPER_PARTIAL_TP_RATIO*100:.0f}% at TP, remainder rides {SCALPER_PARTIAL_TP_TRAIL_MULT:.0f}×ATR trail\n"
        f"  Keltner: close > hl2+{KELTNER_ATR_MULT:.0f}×ATR → +{KELTNER_SCORE_BONUS:.0f}pts bonus\n"
        f"  Watchlist: {len(_watchlist)} pairs | age: {(time.time()-_watchlist_at)/60:.0f}min\n"
        f"\n🌙 <b>Moonshot</b>  [bot-monitored]\n"
        f"  Max: {ALT_MAX_TRADES} trades | Budget: max($2, {MOONSHOT_BUDGET_PCT*100:.0f}% of balance)\n"
        f"  SL: -{MOONSHOT_SL*100:.0f}% | Breakeven: +{MOONSHOT_BREAKEVEN_ACT*100:.0f}%\n"
        f"  Micro TP: {MOONSHOT_MICRO_TP_RATIO*100:.0f}% sold at +{MOONSHOT_MICRO_TP_PCT*100:.0f}% → SL → entry\n"
        f"  Partial TP: {MOONSHOT_PARTIAL_TP_RATIO*100:.0f}% sold at +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}%\n"
        f"  Trail after partial: {MOONSHOT_TRAIL_PCT*100:.0f}% (widens to {MOONSHOT_TRAIL_ATR_WIDE*100:.0f}% once +{MOONSHOT_TRAIL_WIDE_THRESH:.0f}×ATR)\n"
        f"  Timeout: flat {MOONSHOT_TIMEOUT_FLAT_MINS}min | marginal {MOONSHOT_TIMEOUT_MARGINAL_MINS}min | hard {MOONSHOT_TIMEOUT_MAX_MINS}min\n"
        f"\n🔮 <b>Pre-Breakout</b>  [via moonshot slot]\n"
        f"  Patterns: accumulation | squeeze | base-spring\n"
        f"  TP: +{PRE_BREAKOUT_TP*100:.0f}% | SL: -{PRE_BREAKOUT_SL*100:.0f}% | Max: {PRE_BREAKOUT_MAX_HOURS}h\n"
        f"\n🔱 <b>Trinity</b>  [exchange TP + bot SL]\n"
        f"  Pairs: {', '.join(s.replace('USDT','') for s in TRINITY_SYMBOLS)} | Budget: {TRINITY_BUDGET_PCT*100:.0f}% of total\n"
        f"  Entry: drop ≥{TRINITY_DROP_PCT*100:.0f}% (4h/8h) | RSI {TRINITY_MIN_RSI:.0f}–{TRINITY_MAX_RSI:.0f} | vol ≥{TRINITY_VOL_BURST:.1f}× | green candle\n"
        f"  TP: {TRINITY_TP_ATR_MULT}×ATR | SL: {TRINITY_SL_ATR_MULT}×ATR (cap {TRINITY_SL_MAX*100:.1f}%) | Max: {TRINITY_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b>  [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}% | SL: cap-candle anchor | Max: {REVERSAL_MAX_HOURS}h\n"
        f"  Partial TP: {REVERSAL_PARTIAL_TP_RATIO*100:.0f}% sold at +{REVERSAL_PARTIAL_TP_PCT*100:.1f}% → SL moves to entry\n"
        f"  Flat-progress exit: <{REVERSAL_FLAT_PROGRESS*100:.0f}% toward TP after {REVERSAL_FLAT_MINS}min → cut\n"
        f"\n📊 <b>Order Book Depth</b>\n"
        f"  Bid sum within {DEPTH_PCT_RANGE*100:.0f}% must be ≥ {DEPTH_BID_RATIO:.0f}× position value\n"
        f"  ({DEPTH_BID_LEVELS} levels fetched per entry)\n"
        f"\n📐 <b>Kelly Lite Sizing</b>  (score vs threshold={SCALPER_THRESHOLD})\n"
        f"  gap <15: {KELLY_MULT_MARGINAL:.2f}× | gap <30: {KELLY_MULT_SOLID:.2f}× "
        f"| gap <45: {KELLY_MULT_STANDARD:.2f}× | gap ≥45: {KELLY_MULT_HIGH_CONF:.2f}×\n"
        f"\n☠️ <b>Dead Coins</b>\n"
        f"  Scalper floor: ${DEAD_COIN_VOL_SCALPER:,.0f} vol | Moonshot floor: ${DEAD_COIN_VOL_MOONSHOT:,.0f} vol\n"
        f"  Spread cap: {DEAD_COIN_SPREAD_MAX*100:.1f}% | {DEAD_COIN_CONSECUTIVE} fails → {DEAD_COIN_BLACKLIST_HOURS}h blacklist\n"
        f"  Active blacklist: {dead_active} symbols | Pending ({dead_pending} with strikes)\n"
        f"\n🧠 <b>Sentiment</b>: {'✅ on (web search)' if SENTIMENT_ENABLED and WEB_SEARCH_ENABLED else '✅ on (no web search — /ask + journal only)' if SENTIMENT_ENABLED else '⚠️ off'}\n"
        f"\n🧬 <b>Adaptive Learning</b>\n"
        f"  Scalper threshold: {SCALPER_THRESHOLD} base {_adaptive_offsets.get('SCALPER',0):+.0f} offset = {get_effective_threshold('SCALPER'):.0f}\n"
        f"  Moonshot threshold: {MOONSHOT_MIN_SCORE} base {_adaptive_offsets.get('MOONSHOT',0):+.0f} offset = {get_effective_threshold('MOONSHOT'):.0f}\n"
        f"  Scalper budget: {get_effective_budget_pct('SCALPER')*100:.0f}%"
        + (f" (dynamic)" if _dynamic_scalper_budget else " (static)") + "\n"
        f"  Moonshot budget: {get_effective_budget_pct('MOONSHOT')*100:.0f}%"
        + (f" (dynamic)" if _dynamic_moonshot_budget else " (static)") + "\n"
        f"  Maturity filter: penalty >{MATURITY_THRESHOLD*100:.0f}% (scalper) >{MATURITY_MOONSHOT_THRESHOLD*100:.0f}% (moon)\n"
        f"  Fee-aware TP floor: {calc_fee_aware_tp_floor()*100:.2f}%\n"
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


def _cmd_restart():
    telegram("🔄 <b>Restarting...</b> State saved. Railway will redeploy.")
    save_state()
    os._exit(0)


def _cmd_resetstreak():
    global _consecutive_losses, _win_rate_pause_until, _streak_paused_at
    _consecutive_losses    = 0
    _win_rate_pause_until  = 0.0
    _streak_paused_at      = 0.0
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

            if   text == "/pnl":    telegram(build_weekly_message(fetch_mexc_weekly_pnl(), balance))
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
                telegram("⏸️ <b>Paused.</b> No new trades. Existing positions monitored.\n/resume to restart.")
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
           _win_rate_pause_until, _scalper_excluded, _alt_excluded, _api_blacklist, \
           _liquidity_blacklist, _liquidity_fail_count, \
           _adaptive_offsets, _last_rebalance_count, \
           _dynamic_scalper_budget, _dynamic_moonshot_budget

    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Bot — {mode}")

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

    _start_ws_monitor()  # start before watchlist build so open position prices are live

    log.info("📋 Building initial watchlist...")
    build_watchlist(fetch_tickers())

    startup_balance = get_available_balance()
    log.info(f"💰 Starting balance: ${startup_balance:.2f} USDT")
    telegram(
        f"🚀 <b>MEXC Bot Started</b> [{mode}]\n━━━━━━━━━━━━━━━\n"
        f"Balance: <b>${startup_balance:.2f} USDT</b>\n"
        f"\n🟢 <b>Scalper</b> (max {SCALPER_MAX_TRADES} × {get_effective_budget_pct('SCALPER')*100:.0f}%)\n"
        f"  TP/SL: dynamic (signal-aware ATR×mult, candle-capped, noise-floored)\n"
        f"  TP range: {SCALPER_TP_MIN*100:.1f}–{SCALPER_TP_MAX*100:.0f}% | SL range: {SCALPER_SL_MIN*100:.1f}–{SCALPER_SL_MAX*100:.0f}%\n"
        f"  Entry threshold: score ≥ {SCALPER_THRESHOLD} | 1h vol ≥ ${SCALPER_MIN_1H_VOL:,}\n"
        f"  Trail: +{SCALPER_TRAIL_ACT*100:.0f}% → {SCALPER_TRAIL_PCT*100:.1f}% trail\n"
        f"  Breakeven: score ≥ {SCALPER_BREAKEVEN_SCORE} → lock at +{SCALPER_BREAKEVEN_ACT*100:.1f}%\n"
        f"  Symbol cooldown: {SCALPER_SYMBOL_COOLDOWN//60}min after SL\n"
        f"  Circuit breakers: daily -{SCALPER_DAILY_LOSS_PCT*100:.0f}% | {MAX_CONSECUTIVE_LOSSES} consecutive losses\n"
        f"  Watchlist: top {WATCHLIST_SIZE} pairs, refresh every {WATCHLIST_TTL//60}min "
        f"(+early rebuild on BTC ≥{BTC_REBOUND_PCT*100:.0f}% rebound)\n"
        f"\n🌙 <b>Moonshot</b> (max {ALT_MAX_TRADES} trades, {MOONSHOT_BUDGET_PCT*100:.0f}% each) [bot-monitored]\n"
        f"  SL: -{MOONSHOT_SL*100:.0f}% | Micro TP: {MOONSHOT_MICRO_TP_RATIO*100:.0f}% @ +{MOONSHOT_MICRO_TP_PCT*100:.0f}% → SL entry\n"
        f"  Partial TP: +{MOONSHOT_PARTIAL_TP_PCT*100:.0f}% then {MOONSHOT_TRAIL_PCT*100:.0f}% trail | max {MOONSHOT_MAX_HOURS}h\n"
        f"  Pre-breakout: accumulation/squeeze/base patterns → +{PRE_BREAKOUT_TP*100:.0f}%/-{PRE_BREAKOUT_SL*100:.0f}% | {PRE_BREAKOUT_MAX_HOURS}h\n"
        f"\n🔱 <b>Trinity</b> ({TRINITY_BUDGET_PCT*100:.0f}%) [exchange TP + bot SL]\n"
        f"  {'/'.join(s.replace('USDT','') for s in TRINITY_SYMBOLS)} | drop ≥{TRINITY_DROP_PCT*100:.0f}% | RSI {TRINITY_MIN_RSI:.0f}–{TRINITY_MAX_RSI:.0f} | max {TRINITY_MAX_HOURS}h\n"
        f"\n🔄 <b>Reversal</b> (5%) [bot-monitored]\n"
        f"  TP: +{REVERSAL_TP*100:.1f}%  SL: -{REVERSAL_SL*100:.1f}%  max {REVERSAL_MAX_HOURS}h\n"
        f"\n🧠 <b>AI</b>: {'✅ Haiku + web search' if SENTIMENT_ENABLED and WEB_SEARCH_ENABLED else '✅ Haiku only (/ask + journal)' if SENTIMENT_ENABLED else '⚠️ disabled (set ANTHROPIC_API_KEY)'}\n"
        f"  Cache: {SENTIMENT_CACHE_MINS}min | Bonus: +{SENTIMENT_MAX_BONUS}pts | Penalty: -{SENTIMENT_MAX_PENALTY}pts\n"
        f"\n🧬 <b>Adaptive Learning</b>: ✅ enabled\n"
        f"  Maturity filter | Momentum-decay exit | Rolling threshold tuning\n"
        f"  Fee-aware TP floor: {calc_fee_aware_tp_floor()*100:.2f}% | Budget rebalancing every {PERF_REBALANCE_TRADES} trades\n"
        f"\n<i>/status · /metrics · /pnl · /logs · /config · /pause · /resume · /close · /restart · /resetstreak · /ask</i>"
    )
    return startup_balance


def run():
    global _last_rotation_scan, _watchlist, _watchlist_at, \
           _last_rebound_rebuild, \
           _scalper_excluded, _alt_excluded, _btc_ema_gap, \
           _streak_paused_at, _consecutive_losses, _win_rate_pause_until, \
           _paused

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
                    except Exception:
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

            # Rebuild watchlist every WATCHLIST_TTL seconds (10 min)
            if time.time() - _watchlist_at >= WATCHLIST_TTL:
                log.info("📋 Watchlist TTL expired — rebuilding...")
                build_watchlist(tickers if tickers is not None else fetch_tickers())

            # ── BTC Rebound Detector — early watchlist rebuild ────
            # On a coordinated rebound day, coins can go from flat to +30% in
            # under 10 minutes. If BTC confirms an upward thrust (two consecutive
            # green candles of meaningful size), force a rebuild now rather than
            # waiting for the TTL — even if we rebuilt recently.
            # Guard: WATCHLIST_REBOUND_MIN_INTERVAL (5 min) prevents thrashing
            # during a choppy BTC that oscillates around the threshold.
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

            # ── Scalper ───────────────────────────────────────
            budget = round(balance * get_effective_budget_pct("SCALPER"), 2)

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

                        # 3. Hard block — vol spike
                        if btc_regime_ok:
                            tr_full = pd.concat([
                                df_btc["high"] - df_btc["low"],
                                (df_btc["high"] - df_btc["close"].shift(1)).abs(),
                                (df_btc["low"]  - df_btc["close"].shift(1)).abs(),
                            ], axis=1).max(axis=1)
                            atr_series  = tr_full.ewm(alpha=1.0 / 14, adjust=False).mean()
                            btc_atr_now = float(atr_series.iloc[-1])
                            btc_atr_avg = float(atr_series.iloc[-41:-1].mean())
                            if btc_atr_avg > 0 and btc_atr_now > btc_atr_avg * BTC_REGIME_VOL_MULT:
                                btc_regime_ok = False
                                log.info(f"🔴 BTC regime: vol spike "
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
                    # Stash the kelly multiplier that was applied so open_position
                    # can show it in the Telegram message without recomputing.
                    gap = opp.get("score", SCALPER_THRESHOLD) - SCALPER_THRESHOLD
                    opp["kelly_mult"] = (KELLY_MULT_HIGH_CONF if gap >= 45
                                         else KELLY_MULT_STANDARD if gap >= 30
                                         else KELLY_MULT_SOLID    if gap >= 15
                                         else KELLY_MULT_MARGINAL)
                    log.info(f"💰 [SCALPER] Risk budget: ${trade_budget:.2f} "
                             f"(Kelly {opp['kelly_mult']:.2f}× | 1% risk @ SL {pre_sl*100:.2f}%, "
                             f"cap ${round(balance*get_effective_budget_pct('SCALPER'),2):.2f})")
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
                        if reason == "PARTIAL_TP":
                            # Note 11 — sell 30%, remainder rides wider ATR trail
                            execute_partial_tp(trade)
                            # Trade stays live — do NOT remove from scalper_trades
                        elif reason in ("STOP_LOSS", "TRAILING_STOP", "FLAT_EXIT", "TIMEOUT"):
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
                                    rot_gap = best_opp.get("score", SCALPER_THRESHOLD) - SCALPER_THRESHOLD
                                    best_opp["kelly_mult"] = (
                                        KELLY_MULT_HIGH_CONF if rot_gap >= 45 else
                                        KELLY_MULT_STANDARD  if rot_gap >= 30 else
                                        KELLY_MULT_SOLID     if rot_gap >= 15 else
                                        KELLY_MULT_MARGINAL
                                    )
                                    rot_budget, rot_pre_tp, rot_pre_sl, _, _ = calc_risk_budget(best_opp, balance)
                                    new_t = open_position(best_opp, rot_budget, rot_pre_tp, rot_pre_sl, "SCALPER")
                                    if new_t:
                                        scalper_trades.append(new_t)
                                        _scalper_excluded.pop(best_opp["symbol"], None)

            # ── Alt (Trinity / Moonshot / Reversal) ──────────────
            if not _paused and len(alt_trades) < ALT_MAX_TRADES:
                eff_moon_pct = get_effective_budget_pct("MOONSHOT")
                ideal  = round(total_value * eff_moon_pct, 2)
                budget = min(ideal, balance)
                min_alt = MOONSHOT_MIN_NOTIONAL

                if budget < min_alt:
                    log.info(f"💰 Alt budget ${budget:.2f} below floor ${min_alt:.2f} — skipping scan")
                elif tickers is None:
                    log.debug("Alt scan skipped — tickers unavailable this cycle")
                else:
                    log.info(f"💰 Alt budget: ${budget:.2f} "
                             f"(ideal ${ideal:.2f} | free ${balance:.2f} | total ${total_value:.2f})")

                    # ── 1. TRINITY — deep-liquid dip recovery (BTC/ETH/SOL)
                    # Tried first: independent of micro-cap conditions, exchange TP,
                    # no slippage risk, tight spread. Qualifies regardless of alt market.
                    trinity_budget = max(min_alt, min(
                        round(total_value * TRINITY_BUDGET_PCT, 2), balance))
                    opp = find_trinity_opportunity(total_value,
                                                   exclude=_alt_excluded,
                                                   open_symbols=open_symbols)
                    if opp:
                        trade = open_position(opp, trinity_budget,
                                              opp["tp_pct"], opp["sl_pct"],
                                              "TRINITY", max_hours=TRINITY_MAX_HOURS)
                        if trade:
                            alt_trades.append(trade); _alt_excluded = set()
                        else:
                            _alt_excluded.discard(opp["symbol"])

                    # ── 2. MOONSHOT — micro-cap volume burst
                    if not opp:
                        opp = find_moonshot_opportunity(tickers, budget,
                                                        total_value,
                                                        exclude=_alt_excluded,
                                                        open_symbols=open_symbols)
                        if opp:
                            ticker_row = tickers[tickers["symbol"] == opp["symbol"]]
                            if not ticker_row.empty:
                                vol_24h = float(ticker_row["quoteVolume"].iloc[0])
                                vol_pct = min(eff_moon_pct, vol_24h / MOONSHOT_VOL_DIVISOR)
                            else:
                                vol_24h = None
                                vol_pct = eff_moon_pct
                            budget = max(min_alt, min(round(total_value * vol_pct, 2), balance))
                            if vol_pct < eff_moon_pct and vol_24h is not None:
                                log.info(f"💰 [MOONSHOT] Vol-weighted: "
                                         f"{vol_pct*100:.1f}% (24h vol ${vol_24h:,.0f}) → ${budget:.2f}")
                            trade = open_position(opp, budget, MOONSHOT_TP_INITIAL, MOONSHOT_SL,
                                                  "MOONSHOT", max_hours=MOONSHOT_MAX_HOURS)
                            if trade:
                                alt_trades.append(trade); _alt_excluded = set()
                            else:
                                _alt_excluded.discard(opp["symbol"])

                    # ── 3. REVERSAL — oversold micro-cap bounce
                    if not opp:
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

                    # ── 4. PRE_BREAKOUT — accumulation/squeeze/base patterns
                    # Enters BEFORE the spike. Tighter SL (below structure),
                    # better R:R than chasing volume bursts.
                    if not opp:
                        opp = find_prebreakout_opportunity(tickers, budget,
                                                           exclude=_alt_excluded,
                                                           open_symbols=open_symbols)
                        if opp:
                            trade = open_position(opp, budget, PRE_BREAKOUT_TP, PRE_BREAKOUT_SL,
                                                  "MOONSHOT", max_hours=PRE_BREAKOUT_MAX_HOURS)
                            if trade:
                                alt_trades.append(trade); _alt_excluded = set()
                            else:
                                _alt_excluded.discard(opp["symbol"])

                    # ── 4. PRE-BREAKOUT — accumulation/squeeze/base patterns
                    if not opp:
                        opp = find_prebreakout_opportunity(tickers, budget,
                                                           exclude=_alt_excluded,
                                                           open_symbols=open_symbols)
                        if opp:
                            trade = open_position(opp, budget,
                                                  PRE_BREAKOUT_TP, PRE_BREAKOUT_SL,
                                                  "MOONSHOT",  # shares moonshot label for exit logic
                                                  max_hours=PRE_BREAKOUT_MAX_HOURS)
                            if trade:
                                alt_trades.append(trade); _alt_excluded = set()
                            else:
                                _alt_excluded.discard(opp["symbol"])

            for trade in alt_trades[:]:
                should_exit, reason = check_exit(trade)
                if should_exit:
                    if reason in ("PARTIAL_TP", "MICRO_TP"):
                        # Both micro and partial TP: sell a portion, trade stays live
                        execute_partial_tp(trade, micro=(reason == "MICRO_TP"))
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
