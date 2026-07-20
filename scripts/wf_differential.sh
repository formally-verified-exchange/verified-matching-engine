#!/usr/bin/env bash
#
# Cross-artifact well-formedness differential: Lean vs TLA+.
#
# `matcher_lean/MatchingEngine/Order.lean` (Order.wellFormed) and
# `matcher_tla/MatchingEngine.tla` (WellFormed) are two independent
# transcriptions of the prose spec's §2 WF rules. Nothing previously checked
# that they agree, and transcription drift is exactly the failure mode that
# produced the MTL+minQty defect: the prose spec was correct and both formal
# artifacts diverged from it.
#
# This enumerates the full order-shape cross product that `SubmitOrder`
# quantifies over -- 2 x 5 x 4 x 4 x 4 x 2 x 3 x 2 x 3 x 2 x 5 = 230,400
# combinations at PRICES = {1,2,3}, MAX_QTY = 2 -- runs both predicates over
# it, and diffs the accepted sets. A difference in either direction is a
# finding: Lean rejecting a legal order, or Lean admitting an illegal one.
#
# Requires TLA_JAR to point at tla2tools.jar.
#
# NOTE: the two emitters must enumerate the same space. matcher_tla/WFEmit.cfg
# fixes PRICES and MAX_QTY on the TLA side; matcher_lean/WFEmit.lean hardcodes
# the matching lists. If you change one, change the other -- a mismatch shows
# up immediately as a count difference below.

set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TLA_JAR="${TLA_JAR:-${HOME}/tla-plus/tla2tools.jar}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

if [[ ! -f "$TLA_JAR" ]]; then
    echo "error: tla2tools.jar not found at $TLA_JAR (set TLA_JAR)" >&2
    exit 2
fi

echo "==> TLA+: enumerating well-formed order shapes"
cp "$REPO/matcher_tla/MatchingEngine.tla" "$REPO/matcher_tla/WFEmit.tla" \
   "$REPO/matcher_tla/WFEmit.cfg" "$WORK/"
( cd "$WORK" && java -cp "$TLA_JAR" tlc2.TLC \
      -deadlock -workers 1 -metadir "$WORK/meta" \
      -config WFEmit.cfg WFEmit.tla ) > "$WORK/emit.raw" 2>&1

python3 - "$WORK" <<'PYEOF'
import re, sys
work = sys.argv[1]
raw = open(f"{work}/emit.raw").read()
if "BEGIN_WF" not in raw:
    sys.stderr.write("error: TLC produced no shape set:\n" + raw[-2000:])
    sys.exit(2)
body = raw.split('"BEGIN_WF"')[1].split('"END_WF"')[0]
tuples = re.findall(r'<<(.*?)>>', body, re.S)
lines = sorted('|'.join(p.strip().strip('"') for p in t.split(',')) for t in tuples)
open(f"{work}/tla_wf.txt", "w").write("\n".join(lines) + "\n")
print(f"    TLA+ accepts {len(lines)} shapes")
PYEOF

echo "==> Lean: enumerating well-formed order shapes"
( cd "$REPO/matcher_lean" && lake exe wfemit ) > "$WORK/lean.raw"
tail -n +2 "$WORK/lean.raw" | sort > "$WORK/lean_wf.txt"
echo "    Lean accepts $(wc -l < "$WORK/lean_wf.txt") shapes"

only_tla="$(comm -23 "$WORK/tla_wf.txt" "$WORK/lean_wf.txt")"
only_lean="$(comm -13 "$WORK/tla_wf.txt" "$WORK/lean_wf.txt")"

if [[ -z "$only_tla" && -z "$only_lean" ]]; then
    echo
    echo "OK: the two well-formedness predicates agree on every shape."
    exit 0
fi

echo
echo "DIVERGENCE between Lean and TLA+ well-formedness:"
if [[ -n "$only_tla" ]]; then
    echo
    echo "  accepted by TLA+, rejected by Lean ($(wc -l <<< "$only_tla")):"
    head -20 <<< "$only_tla" | sed 's/^/    /'
fi
if [[ -n "$only_lean" ]]; then
    echo
    echo "  accepted by Lean, rejected by TLA+ ($(wc -l <<< "$only_lean")):"
    head -20 <<< "$only_lean" | sed 's/^/    /'
fi
echo
echo "Field order: side|type|tif|price|stopPrice|qty|displayQty|postOnly|minQty|stpGroup|stpPolicy"
exit 1
