#!/usr/bin/env python3
"""Generate seeded TLA+ modules + TLC cfgs from a scenario JSON.

A scenario pre-fills the matching engine book so TLC explores from a
non-empty state. This lets you spend the MAX_ORDERS / MAX_CLOCK budget on
the *interesting* transitions instead of on building up a deep book.

For one scenario, the generator emits:
    MatchingEngine_<name>.tla       — EXTENDS MatchingEngine, Init_Seeded
    <name>__safety.cfg              — safety-only (no target invariant)
    <name>__<target>.cfg            — one cfg per target, for trace extraction

Bounds come from the selected --profile (fast|deep).

Seed-order orderType routing:
    LIMIT / MARKET / MTL   → placed in bidQ or askQ at its price
    STOP_LIMIT / STOP_MARKET → placed in the `stops` set

Usage:
    python3 gen_seeded.py scenarios/deep_book.json --profile fast
    python3 gen_seeded.py scenarios/*.json --profile deep
"""
import argparse
import json
import os
import sys
from collections import defaultdict
from pathlib import Path


REQUIRED_FIELDS = ("id", "side", "orderType", "tif", "qty")

DEFAULT_SAFETY_INVARIANTS = [
    "BookUncrossed",
    "NoGhosts",
    "StatusConsistency",
    "FIFOWithinLevel",
    "NoRestingMarkets",
    "PostOnlyGuarantee",
    "STPGuarantee",
    "NoRestingMTL",
    "NoRestingMinQty",
]

# Targets in scope; used as default if scenario.tlc.targets missing.
DEFAULT_TARGETS = [
    "TargetNoTrade",
    "TargetNoStopTrigger",
    "TargetNoIceberg",
    "TargetNoPartialFill",
    "TargetNoPostOnly",
    "TargetSingleLevel",
    "TargetNoStops",
    "TargetOneSide",
    "TargetNoDepth",
]

STOP_ORDER_TYPES = ("STOP_LIMIT", "STOP_MARKET")


def tla_literal(value):
    """Render a Python value as a TLA+ literal for MakeOrder arguments."""
    if value is None:
        return "NULL"
    if isinstance(value, bool):
        return "TRUE" if value else "FALSE"
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, str):
        return f'"{value}"'
    raise TypeError(f"Cannot render {value!r} as TLA+ literal")


def make_order_call(o, ts):
    """Render MakeOrder(id, side, otype, tif, price, stopPrice, qty,
                        displayQty, postOnly, minQty, stpGroup, stpPolicy, ts).
    """
    args = [
        tla_literal(o["id"]),
        tla_literal(o["side"]),
        tla_literal(o["orderType"]),
        tla_literal(o["tif"]),
        tla_literal(o.get("price")),
        tla_literal(o.get("stopPrice")),
        tla_literal(o["qty"]),
        tla_literal(o.get("displayQty")),
        tla_literal(o.get("postOnly", False)),
        tla_literal(o.get("minQty")),
        tla_literal(o.get("stpGroup")),
        tla_literal(o.get("stpPolicy")),
        tla_literal(ts),
    ]
    return f"MakeOrder({', '.join(args)})"


def validate(scenario):
    if "name" not in scenario:
        raise ValueError("scenario missing 'name'")
    for i, o in enumerate(scenario.get("seed_orders", [])):
        for f in REQUIRED_FIELDS:
            if f not in o:
                raise ValueError(f"seed_orders[{i}] missing '{f}'")
        if o["side"] not in ("BUY", "SELL"):
            raise ValueError(f"seed_orders[{i}].side must be BUY or SELL")
    if "tlc" not in scenario:
        raise ValueError("scenario missing 'tlc'")
    for f in ("prices", "max_qty"):
        if f not in scenario["tlc"]:
            raise ValueError(f"tlc.{f} is required")


def split_seeds(orders):
    """Return (book_by_side_price, stop_list). Each order gets a timestamp
    equal to its position in the original list (1-indexed) so FIFO priority
    matches the declaration order.
    """
    by_side_price = defaultdict(list)
    stops = []
    for idx, o in enumerate(orders):
        ts = idx + 1
        if o["orderType"] in STOP_ORDER_TYPES:
            stops.append((o, ts))
        else:
            if o["orderType"] in ("LIMIT",):
                if o.get("price") is None:
                    raise ValueError(f"order {o['id']}: LIMIT needs a price")
            by_side_price[(o["side"], o.get("price"))].append((o, ts))
    return by_side_price, stops


def emit_tla(scenario):
    name = scenario["name"]
    orders = scenario.get("seed_orders", [])
    by_side_price, stops = split_seeds(orders)

    def case_for(side):
        price_buckets = sorted(
            [(p, lst) for (s, p), lst in by_side_price.items() if s == side and p is not None],
            key=lambda kv: kv[0],
        )
        if not price_buckets:
            return "[p \\in PRICES |-> <<>>]"
        lines = ["[p \\in PRICES |->"]
        for i, (price, lst) in enumerate(price_buckets):
            prefix = "          CASE" if i == 0 else "            []"
            seq = ", ".join(make_order_call(o, ts) for o, ts in lst)
            lines.append(f"{prefix} p = {price} -> <<{seq}>>")
        lines.append("            [] OTHER -> <<>>]")
        return "\n".join(lines)

    if stops:
        stops_expr = "{" + ", ".join(make_order_call(o, ts) for o, ts in stops) + "}"
    else:
        stops_expr = "{}"

    next_id = len(orders) + 1
    next_clock = len(orders) + 1  # first new action starts at this clock

    return f"""---- MODULE MatchingEngine_{name} ----
(***************************************************************************)
(* Auto-generated from scenarios/{name}.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\\ bidQ = {case_for("BUY")}
    /\\ askQ = {case_for("SELL")}
    /\\ stops = {stops_expr}
    /\\ lastTradePrice = NULL
    /\\ postOnlyOK = TRUE
    /\\ stpOK = TRUE
    /\\ nextId = {next_id}
    /\\ clock = {next_clock}
    /\\ lastAction = [type |-> "SeedInit"]

=============================================================================
"""


def _emit_cfg(scenario, profile_bounds, extra_invariant=None, header_comment=""):
    name = scenario["name"]
    tlc = scenario["tlc"]
    seed_count = len(scenario.get("seed_orders", []))

    max_orders = seed_count + profile_bounds["max_orders_extra"]
    max_clock = seed_count + profile_bounds["max_clock_extra"]
    next_rel = tlc.get("next_relation", "NextNoAmend")
    tick_size = tlc.get("tick_size", 1)
    max_qty = tlc["max_qty"]
    prices_str = "{" + ", ".join(str(p) for p in tlc["prices"]) + "}"

    invariants = list(DEFAULT_SAFETY_INVARIANTS)
    if extra_invariant:
        invariants.append(extra_invariant)

    lines = [
        f"\\* Auto-generated from scenarios/{name}.json. Do not edit by hand.",
        f"\\* {header_comment}" if header_comment else "",
        "INIT Init_Seeded",
        f"NEXT {next_rel}",
        "",
        "CONSTANTS",
        "    NULL = NULL",
        f"    TICK_SIZE = {tick_size}",
        f"    MAX_QTY = {max_qty}",
        f"    MAX_ORDERS = {max_orders}",
        f"    MAX_CLOCK = {max_clock}",
        f"    PRICES = {prices_str}",
        "",
        "INVARIANTS",
    ]
    for inv in invariants:
        lines.append(f"    {inv}")
    lines.append("")
    return "\n".join(lines)


def profile_bounds_for(scenario, profile):
    tlc = scenario["tlc"]
    key = f"bounds_{profile}"
    if key in tlc:
        return tlc[key]
    # Legacy / single-profile fallbacks.
    if "max_orders_extra" in tlc and "max_clock_extra" in tlc:
        return {
            "max_orders_extra": tlc["max_orders_extra"],
            "max_clock_extra": tlc["max_clock_extra"],
        }
    # Built-in defaults.
    return {
        "fast": {"max_orders_extra": 2, "max_clock_extra": 4},
        "deep": {"max_orders_extra": 4, "max_clock_extra": 8},
    }[profile]


def emit_all(scenario, out_dir, profile):
    name = scenario["name"]
    tla_path = out_dir / f"MatchingEngine_{name}.tla"
    tla_path.write_text(emit_tla(scenario))

    bounds = profile_bounds_for(scenario, profile)
    targets = scenario["tlc"].get("targets", DEFAULT_TARGETS)
    # Accept legacy singular 'target' field.
    if "target" in scenario["tlc"] and "targets" not in scenario["tlc"]:
        targets = [scenario["tlc"]["target"]]

    safety_path = out_dir / f"{name}__safety.cfg"
    safety_path.write_text(_emit_cfg(
        scenario, bounds,
        extra_invariant=None,
        header_comment=f"Profile: {profile} | Phase A: safety-only (no target)",
    ))

    target_paths = []
    for t in targets:
        p = out_dir / f"{name}__{t}.cfg"
        p.write_text(_emit_cfg(
            scenario, bounds,
            extra_invariant=t,
            header_comment=f"Profile: {profile} | Phase B: target={t}",
        ))
        target_paths.append(p)

    return tla_path, safety_path, target_paths


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("scenarios", nargs="+", help="scenario JSON file(s)")
    ap.add_argument("--profile", choices=["fast", "deep"], default="fast",
                    help="TLC bound profile (default: fast)")
    ap.add_argument("-o", "--out-dir",
                    help="output dir (default: matcher_tla/ next to MatchingEngine.tla)")
    args = ap.parse_args()

    here = Path(__file__).resolve().parent
    out_dir = Path(args.out_dir) if args.out_dir else here.parent

    for path in args.scenarios:
        scenario = json.loads(Path(path).read_text())
        validate(scenario)
        tla_path, safety_path, target_paths = emit_all(scenario, out_dir, args.profile)
        print(f"[{scenario['name']}] {tla_path.name}, {safety_path.name}, "
              f"{len(target_paths)} target cfg(s)")


if __name__ == "__main__":
    main()
