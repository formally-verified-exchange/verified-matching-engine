#!/usr/bin/env python3
"""Convert TLC counterexample traces to JSON for C++ replay harness.

Usage:
    python3 convert_matching_traces.py trace1.txt [trace2.txt ...] -o output_dir/
    python3 convert_matching_traces.py trace.txt  # prints to stdout
"""

import re
import json
import sys
import os
from pathlib import Path


# ── TLC Value Parser ──────────────────────────────────────────────────

def parse_value(s, pos=0):
    """Parse a TLC value starting at position pos. Returns (value, new_pos)."""
    s = s.lstrip() if isinstance(s, str) else s
    pos = _skip_ws(s, pos)
    if pos >= len(s):
        return None, pos

    c = s[pos]

    # String
    if c == '"':
        end = s.index('"', pos + 1)
        return s[pos+1:end], end + 1

    # Sequence <<...>>
    if s[pos:pos+2] == '<<':
        return _parse_seq(s, pos)

    # Set {...}
    if c == '{':
        return _parse_set(s, pos)

    # Record [field |-> val, ...]
    if c == '[':
        return _parse_record(s, pos)

    # Boolean
    if s[pos:pos+4] == 'TRUE':
        return True, pos + 4
    if s[pos:pos+5] == 'FALSE':
        return False, pos + 5

    # NULL model value
    if s[pos:pos+4] == 'NULL':
        return None, pos + 4

    # Number (possibly negative)
    if c == '-' or c.isdigit():
        return _parse_number(s, pos)

    raise ValueError(f"Unexpected char '{c}' at pos {pos}: ...{s[pos:pos+20]}...")


def _skip_ws(s, pos):
    while pos < len(s) and s[pos] in ' \t\n\r':
        pos += 1
    return pos


def _parse_number(s, pos):
    end = pos
    if s[end] == '-':
        end += 1
    while end < len(s) and s[end].isdigit():
        end += 1
    return int(s[pos:end]), end


def _parse_seq(s, pos):
    """Parse <<e1, e2, ...>>"""
    assert s[pos:pos+2] == '<<'
    pos += 2
    pos = _skip_ws(s, pos)
    items = []
    if s[pos:pos+2] == '>>':
        return items, pos + 2
    while True:
        val, pos = parse_value(s, pos)
        items.append(val)
        pos = _skip_ws(s, pos)
        if s[pos:pos+2] == '>>':
            return items, pos + 2
        if s[pos] == ',':
            pos += 1
            pos = _skip_ws(s, pos)


def _parse_set(s, pos):
    """Parse {e1, e2, ...}"""
    assert s[pos] == '{'
    pos += 1
    pos = _skip_ws(s, pos)
    items = []
    if s[pos] == '}':
        return items, pos + 1
    while True:
        val, pos = parse_value(s, pos)
        items.append(val)
        pos = _skip_ws(s, pos)
        if s[pos] == '}':
            return items, pos + 1
        if s[pos] == ',':
            pos += 1
            pos = _skip_ws(s, pos)


def _parse_record(s, pos):
    """Parse [field |-> val, field |-> val, ...]"""
    assert s[pos] == '['
    pos += 1
    pos = _skip_ws(s, pos)
    rec = {}
    if s[pos] == ']':
        return rec, pos + 1
    while True:
        # Field name
        name_end = pos
        while s[name_end] not in ' \t\n|]':
            name_end += 1
        name = s[pos:name_end]
        pos = _skip_ws(s, name_end)
        # |->
        assert s[pos:pos+3] == '|->', f"Expected |-> at {pos}: {s[pos:pos+10]}"
        pos += 3
        pos = _skip_ws(s, pos)
        # Value
        val, pos = parse_value(s, pos)
        rec[name] = val
        pos = _skip_ws(s, pos)
        if s[pos] == ']':
            return rec, pos + 1
        if s[pos] == ',':
            pos += 1
            pos = _skip_ws(s, pos)


# ── TLC Output Parser ────────────────────────────────────────────────

def parse_tlc_trace(text):
    """Parse TLC output into a list of states.
    Returns list of dicts: [{number, action, vars}, ...]
    """
    # Split into state blocks
    state_pattern = re.compile(
        r'^State (\d+): <(.+?)>\s*$',
        re.MULTILINE
    )
    init_pattern = re.compile(
        r'^State 1: <Initial predicate>\s*$',
        re.MULTILINE
    )

    states = []

    # Find all state headers
    headers = []
    for m in re.finditer(r'^State (\d+): <(.+?)>\s*$', text, re.MULTILINE):
        headers.append((int(m.group(1)), m.group(2), m.start(), m.end()))

    # Also check for initial state
    m_init = re.search(r'^State 1: <Initial predicate>\s*$', text, re.MULTILINE)
    if m_init:
        headers.insert(0, (1, 'Init', m_init.start(), m_init.end()))
        # Remove duplicate state 1 if exists
        headers = [(n, a, s, e) for i, (n, a, s, e) in enumerate(headers)
                   if not (i > 0 and n == 1)]

    if not headers:
        return []

    # Extract variable blocks between state headers
    for i, (num, action, start, end) in enumerate(headers):
        # Variable block extends from after header to next state or end markers
        var_start = end
        if i + 1 < len(headers):
            var_end = headers[i + 1][2]
        else:
            # Find end: look for stats line or end of file
            m_end = re.search(r'^\d+ states generated', text[var_start:], re.MULTILINE)
            var_end = var_start + m_end.start() if m_end else len(text)

        var_block = text[var_start:var_end].strip()
        variables = _parse_var_block(var_block)

        # Clean action name
        action_name = action.split(' line ')[0].strip() if ' line ' in action else action

        states.append({
            'number': num,
            'action': action_name,
            'vars': variables
        })

    return states


def parse_tlc_simulate_trace(text):
    """Parse a TLC -simulate trace module (headers: STATE_N == ...).

    Simulate mode writes each random walk as a standalone TLA+ module where
    each state is named STATE_1, STATE_2, etc., separated by blank lines.
    Returns the same [{number, action, vars}, ...] structure as
    parse_tlc_trace so downstream code (convert_trace) can reuse it.
    """
    header_re = re.compile(r'^STATE_(\d+)\s*==\s*$', re.MULTILINE)
    headers = [(int(m.group(1)), m.start(), m.end())
               for m in header_re.finditer(text)]
    if not headers:
        return []

    states = []
    for i, (num, start, end) in enumerate(headers):
        var_start = end
        var_end = headers[i + 1][1] if i + 1 < len(headers) else len(text)
        block = text[var_start:var_end].strip()
        variables = _parse_var_block(block)
        action_name = 'Init' if num == 1 else (
            variables.get('lastAction', {}).get('type') or 'Unknown'
            if isinstance(variables.get('lastAction'), dict) else 'Unknown'
        )
        states.append({'number': num, 'action': action_name, 'vars': variables})
    return states


def _parse_var_block(block):
    """Parse a TLC variable block like:
    /\ bidQ = <<...>>
    /\ askQ = <<...>>
    """
    vars_ = {}
    # Split on /\ at the start of lines
    parts = re.split(r'^\s*/\\', block, flags=re.MULTILINE)
    for part in parts:
        part = part.strip()
        if not part:
            continue
        # Find first = sign
        eq = part.index('=')
        name = part[:eq].strip()
        val_str = part[eq+1:].strip()
        try:
            val, _ = parse_value(val_str, 0)
            vars_[name] = val
        except Exception as e:
            print(f"Warning: Could not parse variable '{name}': {e}", file=sys.stderr)
            vars_[name] = val_str
    return vars_


# ── Action Inference ──────────────────────────────────────────────────

def extract_action(after, prices):
    """Extract action type and parameters from lastAction variable."""
    av = after['vars']
    la = av.get('lastAction')
    if not la or not isinstance(la, dict):
        return {'action': after.get('action', 'Unknown'), 'params': {}}

    atype = la.get('type', 'Unknown')

    if atype == 'SubmitOrder':
        return {
            'action': 'SubmitOrder',
            'params': {
                'id': la.get('id'),
                'side': la.get('side'),
                'price': la.get('price'),
                'quantity': la.get('qty'),
                'orderType': la.get('orderType'),
                'timeInForce': la.get('tif'),
                'stopPrice': la.get('stopPrice'),
                'displayQty': la.get('displayQty'),
                'postOnly': la.get('postOnly', False),
                'minQty': la.get('minQty'),
                'stpGroup': la.get('stpGroup'),
                'stpPolicy': la.get('stpPolicy')
            }
        }
    elif atype == 'CancelOrder':
        return {'action': 'CancelOrder', 'params': {'id': la.get('id')}}
    elif atype == 'AmendOrder':
        return {
            'action': 'AmendOrder',
            'params': {
                'id': la.get('id'),
                'newPrice': la.get('newPrice'),
                'newQty': la.get('newQty')
            }
        }
    elif atype == 'TimeAdvance':
        return {'action': 'TimeAdvance', 'params': {}}
    else:
        return {'action': atype, 'params': {}}


def _collect_orders(book_q, prices):
    """Collect all orders from a bidQ or askQ."""
    orders = {}
    for pi, p in enumerate(prices):
        queue = book_q[pi] if isinstance(book_q, list) else book_q.get(p, [])
        for o in queue:
            if isinstance(o, dict):
                orders[o['id']] = o
    return orders


def _infer_submit(bv, av, prices):
    """Infer SubmitOrder parameters from state diff."""
    new_id = bv['nextId']  # The ID that was assigned

    # Find the new order: either on the book or consumed (lastTradePrice changed)
    # Check book for the new order
    for side_key in ['bidQ', 'askQ']:
        for pi, p in enumerate(prices):
            bq = bv[side_key][pi] if isinstance(bv[side_key], list) else []
            aq = av[side_key][pi] if isinstance(av[side_key], list) else []
            for o in aq:
                if isinstance(o, dict) and o.get('id') == new_id:
                    # Found the new order on the book (it rested)
                    return {
                        'action': 'SubmitOrder',
                        'params': _order_to_params(o)
                    }

    # Order not on book — it was fully consumed or cancelled
    # We need to reconstruct from the state changes
    # The order must have been the aggressor that caused trades
    # With limited info, construct what we can
    # Check if lastTradePrice changed (trade occurred)
    before_orders = {}
    after_orders = {}
    for side_key in ['bidQ', 'askQ']:
        for pi in range(len(prices)):
            for o in (bv[side_key][pi] if isinstance(bv[side_key], list) else []):
                if isinstance(o, dict):
                    before_orders[o['id']] = o
            for o in (av[side_key][pi] if isinstance(av[side_key], list) else []):
                if isinstance(o, dict):
                    after_orders[o['id']] = o

    # Orders that disappeared = filled or cancelled by aggressor
    disappeared = set(before_orders.keys()) - set(after_orders.keys())
    # Orders that appeared with new_id
    appeared_new = {oid for oid in after_orders if oid == new_id}

    # Orders that had qty reduced = partially filled
    partially_filled = {}
    for oid in set(before_orders.keys()) & set(after_orders.keys()):
        bo = before_orders[oid]
        ao = after_orders[oid]
        if ao.get('remainingQty', 0) < bo.get('remainingQty', 0):
            partially_filled[oid] = (bo, ao)

    # Infer the order: we know id = new_id.
    # Reconstruct from what happened to the book.
    # If orders on one side disappeared/reduced → the new order was on the opposite side
    trade_price = av.get('lastTradePrice')
    if trade_price is not None and bv.get('lastTradePrice') != trade_price:
        # Trade occurred
        # Infer side: if bid orders disappeared, new order was SELL
        bid_disappeared = any(before_orders[d].get('side') == 'BUY'
                              for d in disappeared if d in before_orders)
        ask_disappeared = any(before_orders[d].get('side') == 'SELL'
                              for d in disappeared if d in before_orders)
        bid_reduced = any(before_orders[o].get('side') == 'BUY'
                          for o in partially_filled)
        ask_reduced = any(before_orders[o].get('side') == 'SELL'
                          for o in partially_filled)

        if bid_disappeared or bid_reduced:
            side = 'SELL'
        elif ask_disappeared or ask_reduced:
            side = 'BUY'
        else:
            side = 'BUY'  # default

        # Compute quantity: sum of what was consumed
        total_consumed = 0
        for d in disappeared:
            if d in before_orders:
                total_consumed += before_orders[d].get('remainingQty', 0)
        for oid, (bo, ao) in partially_filled.items():
            total_consumed += bo.get('remainingQty', 0) - ao.get('remainingQty', 0)
        # Plus any remainder that rested
        if new_id in after_orders:
            total_consumed += after_orders[new_id].get('remainingQty', 0)

        qty = total_consumed if total_consumed > 0 else 1

        return {
            'action': 'SubmitOrder',
            'params': {
                'id': new_id,
                'side': side,
                'price': trade_price,
                'quantity': qty,
                'orderType': 'LIMIT',
                'timeInForce': 'GTC',
                'stopPrice': None,
                'displayQty': None,
                'postOnly': False,
                'minQty': None,
                'stpGroup': None,
                'stpPolicy': None
            }
        }

    # No trade, order not on book → cancelled (FOK fail, post-only reject, etc.)
    # Check stops
    bstops = set()
    for s in (bv.get('stops') or []):
        if isinstance(s, dict):
            bstops.add(s['id'])
    astops = set()
    for s in (av.get('stops') or []):
        if isinstance(s, dict):
            astops.add(s['id'])
    new_stops = astops - bstops
    if new_id in new_stops:
        # Order went to stops
        for s in av['stops']:
            if isinstance(s, dict) and s['id'] == new_id:
                return {
                    'action': 'SubmitOrder',
                    'params': _order_to_params(s)
                }

    # Fallback: construct minimal order
    return {
        'action': 'SubmitOrder',
        'params': {
            'id': new_id,
            'side': 'BUY',
            'price': 1,
            'quantity': 1,
            'orderType': 'LIMIT',
            'timeInForce': 'GTC',
            'stopPrice': None,
            'displayQty': None,
            'postOnly': False,
            'minQty': None,
            'stpGroup': None,
            'stpPolicy': None
        }
    }


def _order_to_params(o):
    """Convert a TLA+ order record to action params dict."""
    return {
        'id': o.get('id'),
        'side': o.get('side'),
        'price': o.get('price'),
        'quantity': o.get('qty'),
        'orderType': o.get('orderType'),
        'timeInForce': o.get('tif'),
        'stopPrice': o.get('stopPrice'),
        'displayQty': o.get('displayQty'),
        'postOnly': o.get('postOnly', False),
        'minQty': o.get('minQty'),
        'stpGroup': o.get('stpGroup'),
        'stpPolicy': o.get('stpPolicy')
    }


def _infer_cancel(bv, av, prices):
    """Infer CancelOrder parameters from state diff."""
    before_orders = {}
    after_orders = {}
    for side_key in ['bidQ', 'askQ']:
        for pi in range(len(prices)):
            for o in (bv[side_key][pi] if isinstance(bv[side_key], list) else []):
                if isinstance(o, dict):
                    before_orders[o['id']] = o
            for o in (av[side_key][pi] if isinstance(av[side_key], list) else []):
                if isinstance(o, dict):
                    after_orders[o['id']] = o

    disappeared = set(before_orders.keys()) - set(after_orders.keys())
    if disappeared:
        oid = min(disappeared)  # pick one
        return {'action': 'CancelOrder', 'params': {'id': oid}}
    return {'action': 'CancelOrder', 'params': {'id': 0}}


def _infer_amend(bv, av, prices):
    """Infer AmendOrder parameters from state diff."""
    before_orders = {}
    after_orders = {}
    for side_key in ['bidQ', 'askQ']:
        for pi in range(len(prices)):
            for o in (bv[side_key][pi] if isinstance(bv[side_key], list) else []):
                if isinstance(o, dict):
                    before_orders[o['id']] = o
            for o in (av[side_key][pi] if isinstance(av[side_key], list) else []):
                if isinstance(o, dict):
                    after_orders[o['id']] = o

    for oid in set(before_orders.keys()) & set(after_orders.keys()):
        bo = before_orders[oid]
        ao = after_orders[oid]
        if bo != ao:
            new_price = ao.get('price') if ao.get('price') != bo.get('price') else None
            new_qty = ao.get('remainingQty') if ao.get('remainingQty') != bo.get('remainingQty') else None
            return {
                'action': 'AmendOrder',
                'params': {'id': oid, 'newPrice': new_price, 'newQty': new_qty}
            }

    return {'action': 'AmendOrder', 'params': {'id': 0}}


# ── State Projection ─────────────────────────────────────────────────

def project_state(vars_, prices):
    """Project TLA+ state variables to comparable form."""
    bids = []
    for pi, p in enumerate(prices):
        queue = vars_['bidQ'][pi] if isinstance(vars_['bidQ'], list) else []
        if queue:
            entries = []
            for o in queue:
                if isinstance(o, dict):
                    entries.append({
                        'id': o['id'],
                        'remainingQty': o['remainingQty'],
                        'visibleQty': o['visibleQty']
                    })
            if entries:
                bids.append({'price': p, 'orders': entries})

    asks = []
    for pi, p in enumerate(prices):
        queue = vars_['askQ'][pi] if isinstance(vars_['askQ'], list) else []
        if queue:
            entries = []
            for o in queue:
                if isinstance(o, dict):
                    entries.append({
                        'id': o['id'],
                        'remainingQty': o['remainingQty'],
                        'visibleQty': o['visibleQty']
                    })
            if entries:
                asks.append({'price': p, 'orders': entries})

    # Sort: bids descending, asks ascending
    bids.sort(key=lambda x: x['price'], reverse=True)
    asks.sort(key=lambda x: x['price'])

    # Stops
    stop_list = []
    for s in (vars_.get('stops') or []):
        if isinstance(s, dict):
            stop_list.append({
                'id': s['id'],
                'side': s['side'],
                'stopPrice': s.get('stopPrice'),
                'price': s.get('price'),
                'remainingQty': s.get('remainingQty')
            })
    stop_list.sort(key=lambda x: x['id'])

    ltp = vars_.get('lastTradePrice')
    if ltp is None:
        ltp = 0

    # Count orders on book (not stops)
    order_count = sum(len(level['orders']) for level in bids) + \
                  sum(len(level['orders']) for level in asks)

    return {
        'book': {'bids': bids, 'asks': asks},
        'stops': stop_list,
        'lastTradePrice': ltp,
        'orderCount': order_count,
        'stopCount': len(stop_list)
    }


def infer_fills(before, after, prices, agg_side=None):
    """Infer fills from state diff (orders that disappeared or had qty reduced).

    agg_side: 'BUY' or 'SELL' — the aggressor's side, used to order fills by
    price priority (best opposing price first). If None, falls back to
    passiveId-ascending which is wrong for multi-level sweeps.
    """
    bv = before['vars']
    av = after['vars']

    # Only relevant for SubmitOrder (nextId increments)
    if av.get('nextId', 0) <= bv.get('nextId', 0):
        return []

    agg_id = bv['nextId']  # The submitted order's ID

    before_orders = {}
    after_orders = {}
    for side_key in ['bidQ', 'askQ']:
        for pi in range(len(prices)):
            for o in (bv[side_key][pi] if isinstance(bv[side_key], list) else []):
                if isinstance(o, dict):
                    before_orders[o['id']] = o
            for o in (av[side_key][pi] if isinstance(av[side_key], list) else []):
                if isinstance(o, dict):
                    after_orders[o['id']] = o

    fills = []

    # Orders that disappeared = fully filled
    for oid in sorted(set(before_orders.keys()) - set(after_orders.keys())):
        bo = before_orders[oid]
        fills.append({
            'aggressorId': agg_id,
            'passiveId': oid,
            'price': bo.get('price', 0),
            'quantity': bo.get('remainingQty', 0)
        })

    # Orders with reduced qty = partially filled
    for oid in sorted(set(before_orders.keys()) & set(after_orders.keys())):
        bo = before_orders[oid]
        ao = after_orders[oid]
        delta = bo.get('remainingQty', 0) - ao.get('remainingQty', 0)
        if delta > 0:
            fills.append({
                'aggressorId': agg_id,
                'passiveId': oid,
                'price': bo.get('price', 0),
                'quantity': delta
            })

    # Matching visits best opposing price first, then FIFO (lowest passiveId)
    # within each level. For a SELL aggressor, best bid = highest price, so
    # sort price DESC. For a BUY aggressor, best ask = lowest price, so ASC.
    # Tiebreak on passiveId ASC (older orders have lower IDs in these traces).
    if agg_side == 'SELL':
        fills.sort(key=lambda f: (-f['price'], f['passiveId']))
    elif agg_side == 'BUY':
        fills.sort(key=lambda f: (f['price'], f['passiveId']))
    else:
        fills.sort(key=lambda f: f['passiveId'])

    return fills


# ── Main Conversion ──────────────────────────────────────────────────

def infer_prices(states):
    """Infer PRICES set from the trace."""
    prices = set()
    for st in states:
        bq = st['vars'].get('bidQ', [])
        aq = st['vars'].get('askQ', [])
        if isinstance(bq, list):
            prices.update(range(1, len(bq) + 1))
    return sorted(prices) if prices else [1, 2, 3]


def _seed_order_to_params(o, ts):
    """Normalize a scenario seed order into the trace step-params shape
    that conformance_harness.mapParams() already knows how to consume.
    """
    return {
        'id': o['id'],
        'side': o['side'],
        'price': o.get('price'),
        'quantity': o['qty'],
        'orderType': o['orderType'],
        'timeInForce': o['tif'],
        'stopPrice': o.get('stopPrice'),
        'displayQty': o.get('displayQty'),
        'postOnly': o.get('postOnly', False),
        'minQty': o.get('minQty'),
        'stpGroup': o.get('stpGroup'),
        'stpPolicy': o.get('stpPolicy'),
    }


def convert_trace(text, source_name='unknown', scenario=None, simulate=False):
    """Convert a TLC trace text to JSON trace format.

    If `scenario` is provided (parsed scenario JSON), its seed_orders are
    embedded under metadata.seed so the harness can submit them before
    replaying the TLC-generated steps.

    If `simulate` is True, parse as a TLC -simulate trace module
    (STATE_N ==) rather than a counterexample (State N: <Action>).
    """
    states = parse_tlc_simulate_trace(text) if simulate else parse_tlc_trace(text)
    if not states:
        return None

    prices = infer_prices(states)

    steps = []
    for i in range(1, len(states)):
        before = states[i - 1]
        after = states[i]

        action_info = extract_action(after, prices)
        fills = infer_fills(before, after, prices,
                            agg_side=action_info.get('params', {}).get('side'))
        projected = project_state(after['vars'], prices)

        step = {
            'step': i,
            'action': action_info['action'],
            'params': action_info['params'],
            'projected_state': projected
        }
        if fills:
            step['fills'] = fills

        steps.append(step)

    metadata = {
        'source': 'counterexample',
        'trace_id': source_name,
        'state_count': len(states),
        'prices': prices,
    }
    if scenario is not None:
        metadata['scenario'] = scenario.get('name')
        metadata['seed'] = [
            _seed_order_to_params(o, i + 1)
            for i, o in enumerate(scenario.get('seed_orders', []))
        ]

    return {
        'metadata': metadata,
        'steps': steps
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Convert TLC traces to JSON')
    parser.add_argument('files', nargs='+', help='TLC trace files')
    parser.add_argument('-o', '--output-dir', help='Output directory (default: stdout)')
    parser.add_argument('--seed', help='Scenario JSON whose seed_orders should be '
                                       'embedded in metadata.seed for the harness to replay first')
    parser.add_argument('--simulate', action='store_true',
                        help='Parse TLC -simulate trace format (STATE_N ==) '
                             'instead of counterexample format')
    args = parser.parse_args()

    scenario = json.loads(Path(args.seed).read_text()) if args.seed else None

    for filepath in args.files:
        text = open(filepath).read()
        name = Path(filepath).stem
        result = convert_trace(text, name, scenario=scenario, simulate=args.simulate)
        if result is None:
            print(f"Warning: No trace found in {filepath}", file=sys.stderr)
            continue

        json_str = json.dumps(result, indent=2)

        if args.output_dir:
            os.makedirs(args.output_dir, exist_ok=True)
            out_path = os.path.join(args.output_dir, f"{name}.json")
            with open(out_path, 'w') as f:
                f.write(json_str + '\n')
            print(f"Wrote {out_path} ({len(result['steps'])} steps)", file=sys.stderr)
        else:
            print(json_str)


if __name__ == '__main__':
    main()
