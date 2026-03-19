"""
MEXC Scalping Bot — Replit edition with Telegram notifications
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SETUP: Fill in your MEXC API details below, then hit Run.
       Leave PAPER_TRADE = True until you've watched it work for a few days.
"""

import time, hmac, hashlib, logging, requests
import pandas as pd
import numpy as np
from datetime import datetime, timezone

# ═══════════════════════════════════════════════════════════════
#  CONFIG — edit these values before running
# ═══════════════════════════════════════════════════════════════

MEXC_API_KEY    = "mx0vglg1LIlEl98JhQ"       # from MEXC > Profile > API Management
MEXC_API_SECRET = "2b53b21288c8494bbec5e0cc7f34d8c2"    # same place

PAPER_TRADE      = True      # ← keep True for now! Change to False for real money
PAPER_BALANCE    = 50.0     # Simulated USDT balance for paper trading
TAKE_PROFIT_PCT  = 0.020    # 2.0% profit target
STOP_LOSS_PCT   = 0.015     # 1.5% loss limit
SCAN_INTERVAL   = 60        # seconds between market scans (when not in a trade)
MIN_VOLUME_USDT = 500_000   # ignore pairs with low liquidity

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

trade_history      = []
open_trade         = None
last_heartbeat_at  = 0      # timestamp of last hourly heartbeat
last_daily_summary = ""     # date string of last daily summary (e.g. "2024-01-15")
last_top_pair      = None   # best pair seen in last scan, for heartbeat

# ── Telegram ───────────────────────────────────────────────────

def telegram(msg: str):
    """Send a message to Telegram. Fails silently so the bot never crashes."""
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

# ── Balance ────────────────────────────────────────────────────

def get_available_balance() -> float:
    """Fetch free USDT balance. Returns PAPER_BALANCE in paper mode."""
    if PAPER_TRADE:
        # In paper mode, simulate balance shrinking/growing with trade history
        pnl = sum(t["pnl_usdt"] for t in trade_history)
        return round(PAPER_BALANCE + pnl, 2)
    try:
        data = private_get("/api/v3/account")
        for b in data.get("balances", []):
            if b["asset"] == "USDT":
                balance = float(b["free"])
                log.info(f"💰 Available balance: ${balance:.2f} USDT")
                return balance
        log.warning("USDT balance not found in account response.")
        return 0.0
    except Exception as e:
        log.error(f"Failed to fetch balance: {e}")
        return 0.0

# ── Indicators ─────────────────────────────────────────────────

def rsi(series, period=14):
    delta = series.diff()
    gain  = delta.clip(lower=0).rolling(period).mean()
    loss  = (-delta.clip(upper=0)).rolling(period).mean()
    rs    = gain / loss.replace(0, np.nan)
    return 100 - (100 / (1 + rs))

# ── Pair scoring ───────────────────────────────────────────────

def score_pair(symbol):
    try:
        data = public_get("/api/v3/klines", {"symbol": symbol, "interval": "5m", "limit": 60})
        df = pd.DataFrame(data, columns=[
            "open_time","open","high","low","close","volume",
            "close_time","quote_volume","trades","taker_buy_base","taker_buy_quote","ignore"
        ])
        for col in ["close","volume"]:
            df[col] = pd.to_numeric(df[col])

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
        vol_ratio = volume.iloc[-1] / avg_vol if avg_vol > 0 else 1
        vol_score = min(30, (vol_ratio - 1) * 15) if vol_ratio > 1 else 0

        return {
            "symbol":    symbol,
            "score":     round(rsi_score + ma_score + vol_score, 2),
            "rsi":       round(r, 2),
            "vol_ratio": round(vol_ratio, 2),
            "price":     close.iloc[-1],
        }
    except Exception as e:
        log.debug(f"Error scoring {symbol}: {e}")
        return None

# ── Market scanner ─────────────────────────────────────────────

def find_best_opportunity(exclude=None):
    log.info("🔍 Scanning market for opportunities...")
    data = public_get("/api/v3/ticker/24hr")
    df   = pd.DataFrame(data)
    df   = df[df["symbol"].str.endswith("USDT")].copy()
    df["quoteVolume"]        = pd.to_numeric(df["quoteVolume"],        errors="coerce")
    df["priceChangePercent"] = pd.to_numeric(df["priceChangePercent"], errors="coerce")
    df   = df[df["quoteVolume"] >= MIN_VOLUME_USDT]
    df["abs_change"] = df["priceChangePercent"].abs()
    df   = df[df["abs_change"] > 0.5]
    if exclude:
        df = df[df["symbol"] != exclude]

    candidates = df.sort_values("quoteVolume", ascending=False).head(80)["symbol"].tolist()[:40]

    scores = []
    for sym in candidates:
        result = score_pair(sym)
        if result and result["score"] > 20:
            scores.append(result)
        time.sleep(0.1)

    if not scores:
        log.info("No strong signals found this scan.")
        return None

    best = sorted(scores, key=lambda x: x["score"], reverse=True)[0]
    last_top_pair = best
    log.info(f"📊 Top pick: {best['symbol']} | Score: {best['score']} | "
             f"RSI: {best['rsi']} | Vol: {best['vol_ratio']}x | Price: {best['price']}")
    return best

# ── Order execution ────────────────────────────────────────────

def get_step_size(symbol):
    try:
        info = public_get("/api/v3/exchangeInfo")
        for s in info.get("symbols", []):
            if s["symbol"] == symbol:
                for f in s.get("filters", []):
                    if f["filterType"] == "LOT_SIZE":
                        return float(f["stepSize"]), float(f["minQty"])
    except:
        pass
    return 0.001, 0.001

def round_qty(qty, step):
    precision = max(0, -int(np.floor(np.log10(step))))
    return round(np.floor(qty / step) * step, precision)

def place_order(symbol, side, qty):
    if PAPER_TRADE:
        log.info(f"📝 [PAPER] {side} {qty} {symbol} @ MARKET")
        return {"orderId": f"PAPER_{int(time.time())}", "paper": True}
    params = {"symbol": symbol, "side": side, "type": "MARKET", "quantity": qty}
    return private_post("/api/v3/order", params)

# ── Trade lifecycle ────────────────────────────────────────────

def open_position(opp):
    symbol  = opp["symbol"]
    price   = opp["price"]

    budget = get_available_balance()
    if budget < 1.0:
        msg = f"⚠️ Insufficient balance: ${budget:.2f} USDT. Bot pausing."
        log.warning(msg)
        telegram(msg)
        return None

    step, min_q = get_step_size(symbol)
    qty = round_qty(budget / price, step)
    if qty < min_q:
        log.warning(f"⚠️  {symbol}: qty {qty} below minimum {min_q}, skipping.")
        return None
    order = place_order(symbol, "BUY", qty)
    if not order:
        return None

    trade = {
        "symbol":      symbol,
        "entry_price": price,
        "qty":         qty,
        "budget_used": round(budget, 2),
        "tp_price":    round(price * (1 + TAKE_PROFIT_PCT), 8),
        "sl_price":    round(price * (1 - STOP_LOSS_PCT),   8),
        "opened_at":   datetime.now(timezone.utc).isoformat(),
        "score":       opp["score"],
    }

    mode = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"
    log.info(f"🟢 Opened: {symbol} | Budget: ${budget:.2f} | Entry: {price:.6f} | "
             f"TP: {trade['tp_price']:.6f} | SL: {trade['sl_price']:.6f}")
    telegram(
        f"🟢 <b>Trade Opened</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:        <b>{symbol}</b>\n"
        f"Budget:      <b>${budget:.2f} USDT</b>\n"
        f"Entry:       <b>${price:.6f}</b>\n"
        f"Take profit: <b>${trade['tp_price']:.6f}</b>  (+2%)\n"
        f"Stop loss:   <b>${trade['sl_price']:.6f}</b>  (-1.5%)\n"
        f"Signal score: {opp['score']} | RSI: {opp['rsi']} | Vol: {opp['vol_ratio']}x"
    )
    return trade

def monitor_and_exit(trade):
    symbol = trade["symbol"]
    try:
        ticker = public_get("/api/v3/ticker/price", {"symbol": symbol})
        price  = float(ticker["price"])
    except Exception as e:
        log.error(f"Price fetch error: {e}")
        return False, ""

    pct = (price - trade["entry_price"]) / trade["entry_price"] * 100

    if price >= trade["tp_price"]:
        log.info(f"🎯 TP hit: {symbol} | +{pct:.2f}% | Price: {price:.6f}")
        return True, "TAKE_PROFIT"
    if price <= trade["sl_price"]:
        log.info(f"🛑 SL hit: {symbol} | {pct:.2f}% | Price: {price:.6f}")
        return True, "STOP_LOSS"

    log.info(f"👀 Holding {symbol} | {pct:+.2f}% | Price: {price:.6f}")
    return False, ""

def close_position(trade, reason):
    place_order(trade["symbol"], "SELL", trade["qty"])
    try:
        ticker     = public_get("/api/v3/ticker/price", {"symbol": trade["symbol"]})
        exit_price = float(ticker["price"])
    except:
        exit_price = trade["tp_price"] if reason == "TAKE_PROFIT" else trade["sl_price"]

    pnl_pct  = (exit_price - trade["entry_price"]) / trade["entry_price"] * 100
    pnl_usdt = (exit_price - trade["entry_price"]) * trade["qty"]

    closed = {**trade, "exit_price": exit_price, "exit_reason": reason,
              "pnl_pct": round(pnl_pct, 4), "pnl_usdt": round(pnl_usdt, 4)}
    trade_history.append(closed)

    # Stats for the notification
    wins      = [t for t in trade_history if t["pnl_pct"] > 0]
    win_rate  = len(wins) / len(trade_history) * 100
    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    if reason == "TAKE_PROFIT":
        emoji, label = "🎯", "Take Profit Hit"
    else:
        emoji, label = "🛑", "Stop Loss Hit"

    telegram(
        f"{emoji} <b>{label}</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Pair:    <b>{trade['symbol']}</b>\n"
        f"Entry:   ${trade['entry_price']:.6f}\n"
        f"Exit:    <b>${exit_price:.6f}</b>\n"
        f"P&L:     <b>{pnl_pct:+.2f}%  (${pnl_usdt:+.2f})</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Session: {len(trade_history)} trades | "
        f"Win rate: {win_rate:.0f}% | "
        f"Total P&L: ${total_pnl:+.2f}"
    )
    log.info(f"📈 Stats | Trades: {len(trade_history)} | "
             f"Win rate: {win_rate:.0f}% | Total P&L: ${total_pnl:+.2f}")

# ── Heartbeat & daily summary ──────────────────────────────────

def send_heartbeat():
    global last_heartbeat_at
    now = time.time()
    if now - last_heartbeat_at < 3600:
        return
    last_heartbeat_at = now

    balance = get_available_balance()
    mode    = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    if open_trade:
        try:
            ticker = public_get("/api/v3/ticker/price", {"symbol": open_trade["symbol"]})
            price  = float(ticker["price"])
            pct    = (price - open_trade["entry_price"]) / open_trade["entry_price"] * 100
            trade_line = (f"In trade: <b>{open_trade['symbol']}</b> | "
                          f"Currently: {pct:+.2f}%")
        except:
            trade_line = f"In trade: <b>{open_trade['symbol']}</b>"
    elif last_top_pair:
        trade_line = (f"Watching: <b>{last_top_pair['symbol']}</b> | "
                      f"Score: {last_top_pair['score']} | "
                      f"RSI: {last_top_pair['rsi']}")
    else:
        trade_line = "No strong signals yet this scan"

    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    trades_today = len([t for t in trade_history if t["closed_at"][:10] == today])

    telegram(
        f"💓 <b>Heartbeat</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Bot is alive and running\n"
        f"Balance: <b>${balance:.2f} USDT</b>\n"
        f"{trade_line}\n"
        f"Trades today: {trades_today}"
    )


def send_daily_summary():
    global last_daily_summary
    today    = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    now_hour = datetime.now(timezone.utc).hour
    if last_daily_summary == today or now_hour != 0:
        return
    last_daily_summary = today

    if not trade_history:
        telegram(
            f"📅 <b>Daily Summary</b>\n"
            f"━━━━━━━━━━━━━━━\n"
            f"No trades placed today.\n"
            f"Bot is scanning but signals weren't strong enough to enter."
        )
        return

    wins      = [t for t in trade_history if t["pnl_pct"] > 0]
    losses    = [t for t in trade_history if t["pnl_pct"] <= 0]
    win_rate  = len(wins) / len(trade_history) * 100
    total_pnl = sum(t["pnl_usdt"] for t in trade_history)
    best      = max(trade_history, key=lambda t: t["pnl_pct"])
    worst     = min(trade_history, key=lambda t: t["pnl_pct"])
    balance   = get_available_balance()
    mode      = "📝 PAPER" if PAPER_TRADE else "💰 LIVE"

    telegram(
        f"📅 <b>Daily Summary</b> [{mode}]\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Trades:    <b>{len(trade_history)}</b>  "
        f"({len(wins)} wins / {len(losses)} losses)\n"
        f"Win rate:  <b>{win_rate:.0f}%</b>\n"
        f"Total P&L: <b>${total_pnl:+.2f}</b>\n"
        f"Balance:   <b>${balance:.2f} USDT</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Best trade:  {best['symbol']} {best['pnl_pct']:+.2f}%\n"
        f"Worst trade: {worst['symbol']} {worst['pnl_pct']:+.2f}%"
    )

# ── Main loop ──────────────────────────────────────────────────

def run():
    global open_trade
    mode = "📝 PAPER TRADING" if PAPER_TRADE else "💰 LIVE TRADING"
    log.info(f"🚀 MEXC Scalping Bot — {mode}")
    log.info(f"   Mode: {mode} | TP: {TAKE_PROFIT_PCT*100}% | SL: {STOP_LOSS_PCT*100}%")

    startup_balance = get_available_balance()
    telegram(
        f"🚀 <b>MEXC Scalping Bot Started</b>\n"
        f"━━━━━━━━━━━━━━━\n"
        f"Mode:         <b>{mode}</b>\n"
        f"Balance:      <b>${startup_balance:.2f} USDT</b>\n"
        f"Take profit:  +{TAKE_PROFIT_PCT*100:.1f}%\n"
        f"Stop loss:    -{STOP_LOSS_PCT*100:.1f}%\n"
        f"Signals:      RSI + EMA crossover + Volume"
    )

    last_excluded = None

    while True:
        try:
            if open_trade is None:
                opp = find_best_opportunity(exclude=last_excluded)
                if opp:
                    open_trade = open_position(opp)
                    last_excluded = None
                else:
                    log.info(f"⏳ No opportunity. Retrying in {SCAN_INTERVAL}s...")
                    time.sleep(SCAN_INTERVAL)
                    continue

            if open_trade:
                should_exit, reason = monitor_and_exit(open_trade)
                if should_exit:
                    last_excluded = open_trade["symbol"]
                    close_position(open_trade, reason)
                    open_trade = None
                    log.info("🔄 Closed. Scanning for next opportunity...")
                    time.sleep(5)
                else:
                    time.sleep(15)
            else:
                time.sleep(SCAN_INTERVAL)

        except KeyboardInterrupt:
            log.info("🛑 Stopped.")
            if open_trade:
                log.warning(f"⚠️  Still holding {open_trade['symbol']} — close manually on MEXC if live!")
            telegram("🛑 <b>Bot stopped.</b> Check Railway — it may need restarting.")
            break
        except Exception as e:
            log.error(f"Error: {e}", exc_info=True)
            telegram(f"⚠️ <b>Bot error:</b> {str(e)[:200]}\nWill retry in 30s.")
            time.sleep(30)

        # ── Heartbeat & daily summary (runs every loop iteration) ─
        send_heartbeat()
        send_daily_summary()

run()
