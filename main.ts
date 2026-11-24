// A from-scratch paper trader for the make.fun replay (agent-fun/replay/v2 protocol).
// One hello precedes the stream; each batch maps to a single slot, and onBatch emits the orders
// decided on that slot. We enter once a maturing curve's tape shows buy pressure building, leave
// the entire position on a stop, take-profit, trailing stop, or time limit, and sprinkle paced
// probe round trips so the distinct-coin guardrail is met. Fully deterministic: no clock, no
// randomness, no environment reads; loops only over batch events and insertion-ordered maps.

import { runBot, LAMPORTS_PER_SOL } from './vendor/makefun-bot.ts';
import type { Batch, Bot, BotState, OrderInput, Pubkey } from './vendor/makefun-bot.ts';

const LAM = Number(LAMPORTS_PER_SOL); // 1e9 lamports per SOL
const CURVE_FEE = 0.0125;

// Every tunable lives in one table, with the starting values specified by the brief;
// later passes adjust only these numbers, never the surrounding logic.
const P = {
  window: 30,          // entry lookback, in slots
  keep: 60,            // tape retention, in slots
  minAge: 200,         // slots since CreateEvent before an entry
  minBuys: 3,          // buy trades in the window
  minBuyers: 3,        // distinct buying wallets in the window
  minNetSol: 2.0,      // net SOL inflow in the window
  minPriceUp: 0.05,    // minimum price rise from window start
  maxPriceUp: 0.25,    // maximum price rise from window start
  nearHigh: 0.95,      // price must be at least this share of window high
  accel: 0,            // newer-half net inflow >= this * older-half net inflow
  minRqSol: 2,         // real SOL reserve lower bound at entry
  maxRqSol: 5,         // real SOL reserve upper bound at entry (early curves have the edge)
  mainBuySol: 0.05,    // SOL spent per main entry
  minBuySol: 0.011,    // never send a buy smaller than this
  stop: 0.90,          // sell when close value <= cost * stop
  take: 1.35,          // sell when close value >= cost * take
  trailArm: 1.06,      // arm trailing stop once peak >= cost * trailArm
  trail: 0.90,         // sell when close value < peak * trail
  maxHold: 900,        // sell after this many slots held
  maxMain: 2,          // main positions (3 slots left for probes)
  cooldown: 200,       // slots to wait before re-entering the same mint
  buySlipBps: 500,     // buy slippage
  sellSlipBps: 10000,  // sell slippage (max)
  targetCoins: 22,     // pacing target for distinct coins
  paceSecs: 14400,     // 6-hour window in seconds
  probeSol: 0.012,     // SOL per probe buy (>= the 0.01 round-trip bar)
  probeMinRq: 2,       // real SOL reserve lower bound for a probe
  maxProbes: 2,        // probes in flight
};

interface Trade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}
interface Tape {
  created: number | null;
  trades: Trade[];
  lastExit: number;
}
interface Held {
  opened: number;
  peakValue: number;
  filled: boolean;
  exiting: boolean;
  lastValue: number;
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
/** Probe round trips in flight, by mint. */
const probes = new Map<Pubkey, boolean>();
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
}

/** Momentum entry test on a mint's rolling tape. */
function entrySignal(t: Tape, now: number, rqSol: number): boolean {
  if (rqSol < P.minRqSol || rqSol > P.maxRqSol) return false;
  if (t.created === null || now - t.created < P.minAge) return false;
  const from = now - P.window;
  const mid = now - P.window / 2;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const buyers = new Set<string>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      buyers.add(tr.user);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < P.minBuys || buyers.size < P.minBuyers) return false;
  const net = buySol - sellSol;
  if (net <= P.minNetSol) return false;
  if (startPrice <= 0) return false;
  const up = last / startPrice - 1;
  if (up < P.minPriceUp || up > P.maxPriceUp) return false;
  if (last < high * P.nearHigh) return false;
  if (netNew < P.accel * netOld) return false;
  return true;
}

const bot: Bot = {
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAM;
    const orders: OrderInput[] = [];

    // Track this bot's own filled orders (harness closes start with '_').
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        if (f.side === 'buy') myCoins.add(f.mint);
      }
    }

    // Fold this slot's events into tapes and block-time pacing.
    const traded = new Set<Pubkey>();
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        const sol = Number(e.sol_amount) / LAM;
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol,
          user: e.user,
          price: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
        });
        traded.add(e.mint);
      }
    }
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - P.keep) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    // 1) Whole-position exits, using mark reserves when present.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          if (h.filled) tapeOf(mint).lastExit = now;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      const tokens = Number(pos.token_amount);
      const value = ((tokens * vq) / (vt + tokens) / LAM) * (1 - CURVE_FEE) - tx;
      const cost = Number(pos.cost_lamports) / LAM;
      if (value > h.peakValue) h.peakValue = value;
      h.lastValue = value;
      let exit = h.exiting;
      if (!exit && value <= cost * P.stop) exit = true;
      if (!exit && value >= cost * P.take) exit = true;
      if (!exit && h.peakValue >= cost * P.trailArm && value < h.peakValue * P.trail) exit = true;
      if (!exit && now - h.opened > P.maxHold) exit = true;
      if (!exit) continue;
      h.exiting = true;
      if (pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: P.sellSlipBps });
    }

    // 2) Probe round trips: sell the whole position on the next batch it becomes visible.
    for (const [mint] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: P.sellSlipBps });
    }

    // 3) Momentum entries.
    let free = Number(state.freeCashLamports()) / LAM;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let mainLeft = P.maxMain - held.size;
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint) || held.has(mint)) continue;
      const t = tapes.get(mint)!;
      if (now - t.lastExit < P.cooldown) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAM;
      if (!entrySignal(t, now, rqSol)) continue;
      if (slotsLeft <= 0 || mainLeft <= 0) continue;
      let amount = Math.min(P.mainBuySol, Number(state.maxBuyLamports(mint)) / LAM);
      if (amount > free - tx) amount = free - tx;
      if (amount < P.minBuySol) continue;
      orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(amount * LAM)), max_slippage_bps: P.buySlipBps });
      held.set(mint, { opened: now, peakValue: 0, filled: false, exiting: false, lastValue: 0 });
      free -= amount + tx;
      slotsLeft--;
      mainLeft--;
    }

    // 4) Guardrail pacing: open a probe when distinct coins lag block-time pace.
    if (probes.size < P.maxProbes && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / P.paceSecs);
      const needCoins = myCoins.size < Math.ceil(P.targetCoins * pace);
      const needFills = myFills < Math.ceil(P.targetCoins * pace * 2);
      if (needCoins || needFills) {
        const minRq = (P.probeSol * Number(10000)) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= P.maxProbes) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAM < Math.max(P.probeMinRq, minRq)) continue;
          if (free < P.probeSol + 2 * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(P.probeSol * LAM)), max_slippage_bps: P.buySlipBps });
          probes.set(mint, false);
          free -= P.probeSol + tx;
        }
      }
    }

    return orders;
  },
};

await runBot(bot);
