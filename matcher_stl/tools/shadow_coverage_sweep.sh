#!/usr/bin/env bash
# shadow_coverage_sweep.sh — massive shadow run under gcov instrumentation.
#
# Runs N seeds × M steps sequentially against build-coverage/shadow_test so
# .gcda accumulates across every seed. Aggregates per-seed stats, then
# produces gcovr reports for engine.h coverage.
#
# Usage:
#   ./shadow_coverage_sweep.sh [SEEDS] [STEPS] [OUT_DIR]
# Defaults: SEEDS=64, STEPS=200000, OUT=shadow_runs/cov_<ts>
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

SEEDS="${1:-64}"
STEPS="${2:-200000}"
OUT_DIR="${3:-shadow_runs/cov_$(date +%Y%m%d-%H%M%S)}"
BIN="$PWD/build-coverage/shadow_test"

if [[ ! -x "$BIN" ]]; then echo "missing $BIN" >&2; exit 1; fi

mkdir -p "$OUT_DIR/per_seed"
SUMMARY="$OUT_DIR/summary.tsv"
: > "$SUMMARY"

echo "=== shadow coverage sweep ==="
echo "  Seeds: $SEEDS"
echo "  Steps: $STEPS per seed"
echo "  Out:   $OUT_DIR"
echo "  Bin:   $BIN"
echo

# Reset .gcda so this sweep starts from zero coverage.
find build-coverage -name '*.gcda' -delete

start_wall=$(date +%s.%N)
for ((s=1; s<=SEEDS; s++)); do
    log="$OUT_DIR/per_seed/seed_${s}.log"
    # Serial execution so .gcda writes don't race. Coverage build is ~3–5×
    # slower than Release; stays at ~300k steps/sec.
    "$BIN" "$STEPS" "$s" > "$log" 2>&1 || true

    bugs=$(grep -oP 'Divergences total: \K[0-9]+' "$log" | head -1)
    result=$(grep -oP 'Result:\s+\K\w+' "$log" | head -1)
    steps_done=$(grep -oP 'Steps run:\s+\K[0-9]+' "$log" | head -1)
    peakOrd=$(grep -oP 'Peak book orders:\s+\K[0-9]+' "$log" | head -1)
    peakBid=$(grep -oP 'Peak bid levels:\s+\K[0-9]+' "$log" | head -1)
    peakAsk=$(grep -oP 'Peak ask levels:\s+\K[0-9]+' "$log" | head -1)
    sweepB=$(grep -oP 'Sweep events \(bid→0\):\s+\K[0-9]+' "$log" | head -1)
    sweepA=$(grep -oP 'Sweep events \(ask→0\):\s+\K[0-9]+' "$log" | head -1)
    trades=$(grep -oP 'Cumulative trades:\s+\K[0-9]+' "$log" | head -1)
    cross=$(grep -oP 'Book-cross violations:\s+\K[0-9]+' "$log" | head -1)
    maxF=$(grep -oP 'Max fills in one step:\s+\K[0-9]+' "$log" | head -1)
    tput=$(grep -oP 'Throughput:\s+\K[0-9]+' "$log" | head -1)

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$s" "${result:-?}" "${bugs:-?}" "${steps_done:-0}" "${peakOrd:-0}" \
        "${peakBid:-0}" "${peakAsk:-0}" "${sweepB:-0}" "${sweepA:-0}" \
        "${trades:-0}" "${cross:-0}" "${maxF:-0}" "${tput:-0}" >> "$SUMMARY"

    # Progress
    if (( s % 8 == 0 )); then
        echo "  ...seed $s / $SEEDS done"
    fi
done
end_wall=$(date +%s.%N)
total_sec=$(awk "BEGIN{printf \"%.2f\", $end_wall - $start_wall}")

echo
echo "=== aggregate ==="
awk -F'\t' -v ts="$total_sec" '
BEGIN {
    pass=0; fail=0; bugs=0; steps=0; trades=0; peakOrd=0; peakBid=0; peakAsk=0;
    sweepB=0; sweepA=0; cross=0; maxF=0;
}
{
    if ($2=="PASS") pass++; else fail++;
    bugs+=$3; steps+=$4;
    if ($5>peakOrd) peakOrd=$5;
    if ($6>peakBid) peakBid=$6;
    if ($7>peakAsk) peakAsk=$7;
    sweepB+=$8; sweepA+=$9;
    trades+=$10;
    cross+=$11;
    if ($12>maxF) maxF=$12;
}
END {
    printf "seeds:              %d (PASS=%d FAIL=%d)\n", NR, pass, fail;
    printf "total BUGs:         %d\n", bugs;
    printf "total steps:        %d\n", steps;
    printf "total trades:       %d\n", trades;
    printf "peak orders:        %d\n", peakOrd;
    printf "peak bid levels:    %d\n", peakBid;
    printf "peak ask levels:    %d\n", peakAsk;
    printf "sweep (bid→0):      %d\n", sweepB;
    printf "sweep (ask→0):      %d\n", sweepA;
    printf "max fills in step:  %d\n", maxF;
    printf "book-cross:         %d\n", cross;
    printf "wall time:          %s s\n", ts;
    printf "throughput overall: %.0f steps/sec\n", (ts>0 ? steps/ts : 0);
}' "$SUMMARY"

echo
echo "=== coverage (gcovr) ==="
gcovr --root "$PWD" \
      --filter "src/engine\.h$" \
      --print-summary \
      --html-details "$OUT_DIR/coverage.html" \
      --txt "$OUT_DIR/coverage.txt" \
      build-coverage 2>&1 | tail -20
echo
echo "HTML report: $OUT_DIR/coverage.html"
echo "TXT  report: $OUT_DIR/coverage.txt"
