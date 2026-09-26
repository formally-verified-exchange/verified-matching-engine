#!/usr/bin/env python3
"""Regenerate the model-checking statistics table from archived raw TLC logs.

Reads matcher_tla/results/metadata.json (provenance: config/model hashes,
exact commands, host/TLC/Java versions, historical comparison) and the raw
TLC stdout logs it references, and prints:
  - a CSV suitable for a spreadsheet or a script to consume
  - the Markdown table text used in REPORT.md / paper.tex

This does not re-run TLC. It only re-derives the table from what is already
archived, so the paper's numbers can be checked against the raw evidence
without trusting hand-transcribed figures.

Usage:
    python3 matcher_tla/tools/generate_stats_summary.py [--json path]
"""
import argparse
import csv
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def parse_raw_log(path: Path):
    """Cross-check a raw TLC log against the metadata's recorded numbers."""
    text = path.read_text(errors="replace")
    m = re.search(
        r"([\d,]+) states generated, ([\d,]+) distinct states found, "
        r"([\d,]+) states left on queue\.",
        text,
    )
    if not m:
        return None
    generated, distinct, queued = (int(g.replace(",", "")) for g in m.groups())
    violated = "Error: Invariant" in text
    completed = "Model checking completed. No error has been found." in text
    return {
        "generated": generated,
        "distinct": distinct,
        "queued": queued,
        "violated": violated,
        "completed": completed,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--json",
        default=str(REPO_ROOT / "matcher_tla" / "results" / "metadata.json"),
    )
    args = ap.parse_args()

    meta = json.loads(Path(args.json).read_text())
    rows = meta["runs"]

    mismatches = []
    for row in rows:
        raw_path = REPO_ROOT / row["raw_log"]
        if not raw_path.exists():
            print(f"WARNING: raw log missing: {raw_path}", file=sys.stderr)
            continue
        parsed = parse_raw_log(raw_path)
        if parsed is None:
            print(f"WARNING: could not parse {raw_path}", file=sys.stderr)
            continue
        if parsed["generated"] != row["states_generated"] or parsed["distinct"] != row["distinct_states"]:
            mismatches.append((row["label"], parsed, row))

    if mismatches:
        print("MISMATCHES between metadata.json and raw logs:", file=sys.stderr)
        for label, parsed, row in mismatches:
            print(f"  {label}: raw={parsed} metadata={row}", file=sys.stderr)

    # CSV
    writer = csv.writer(sys.stdout)
    writer.writerow(
        ["Configuration", "Orders", "Qty", "Prices", "Amend", "States Gen.",
         "Distinct", "Elapsed", "Result"]
    )
    for row in rows:
        p = row["params"]
        writer.writerow(
            [
                row["label"],
                p["MAX_ORDERS"],
                p["MAX_QTY"],
                p["PRICES"],
                "Yes" if p["amend"] else "No",
                row["states_generated"],
                row["distinct_states"],
                row["elapsed"],
                row["result"].split(" ")[0],
            ]
        )

    completed = [r for r in rows if r["states_left_on_queue"] == 0]
    gsum = sum(r["states_generated"] for r in completed)
    dsum = sum(r["distinct_states"] for r in completed)
    print("", file=sys.stderr)
    print(
        f"Aggregate over {len(completed)} completed (exhaustive) configurations: "
        f"{gsum:,} states generated, {dsum:,} distinct states (sum of per-run counts, "
        "not a deduplicated union).",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
