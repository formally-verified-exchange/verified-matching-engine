#!/usr/bin/env bash
# shadow_sweep.sh — parallel seeded shadow_test runner.
#
# Runs N seeds of shadow_test in parallel, each with M steps. Aggregates
# exit codes and BUG counts per seed; writes per-seed logs under OUT_DIR.
#
# Usage:
#   ./shadow_sweep.sh [SEEDS] [STEPS] [JOBS] [OUT_DIR]
#
# Defaults: SEEDS=1000, STEPS=10000000 (10M), JOBS=16, OUT_DIR=shadow_runs/<ts>
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

SEEDS="${1:-1000}"
STEPS="${2:-10000000}"
JOBS="${3:-16}"
OUT_DIR="${4:-shadow_runs/$(date +%Y%m%d-%H%M%S)}"

BIN="$PWD/build-verify/shadow_test"
if [[ ! -x "$BIN" ]]; then
    echo "shadow_test missing at $BIN — build first" >&2
    exit 1
fi

mkdir -p "$OUT_DIR/per_seed"
SUMMARY="$OUT_DIR/summary.tsv"
: > "$SUMMARY"

cat <<EOF
=== shadow_sweep ===
  Seeds:   $SEEDS
  Steps:   $STEPS per seed  (total = $((SEEDS * STEPS)) engine ops)
  Jobs:    $JOBS
  Out:     $OUT_DIR
  Bin:     $BIN
EOF

export BIN OUT_DIR STEPS SUMMARY

run_one() {
    local seed="$1"
    local log="$OUT_DIR/per_seed/seed_${seed}.log"
    "$BIN" "$STEPS" "$seed" > "$log" 2>&1
    local rc=$?
    local bugs knowns result
    bugs=$(grep -c '^  BUG  '   "$log" 2>/dev/null || echo 0)
    knowns=$(grep -c '^  KNOWN ' "$log" 2>/dev/null || echo 0)
    result=$(grep -m1 '^  Result:' "$log" 2>/dev/null | awk '{print $2}')
    [[ -z "$result" ]] && result="?"
    printf '%s\t%s\t%s\t%s\t%s\n' "$seed" "$rc" "$result" "$bugs" "$knowns" >> "$SUMMARY"
    # delete passing logs to save space
    if [[ "$rc" == 0 && "$bugs" == 0 ]]; then rm -f "$log"; fi
}
export -f run_one

seq 1 "$SEEDS" | xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {}

echo
echo "=== summary ==="
awk -F'\t' 'BEGIN{p=0;f=0;bugs=0;knowns=0}
{ if($2==0 && $4==0) p++; else f++; bugs+=$4; knowns+=$5 }
END{ printf "seeds_total    %d\nseeds_clean    %d\nseeds_with_bug %d\ntotal_bugs     %d\ntotal_knowns   %d\n", NR,p,f,bugs,knowns }' "$SUMMARY"

echo
echo "=== seeds with BUGs (first 10) ==="
awk -F'\t' '$4>0 {print}' "$SUMMARY" | head -10
