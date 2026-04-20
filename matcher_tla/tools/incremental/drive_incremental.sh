#!/usr/bin/env bash
# drive_incremental.sh — parallel orchestrator for incremental TLC → C++.
#
# Builds the full list of (scenario, chunk) jobs, then feeds it through
# an xargs worker pool with JOBS parallel workers.  Each worker runs
# produce_chunk.sh + replay_chunk.sh for its assigned chunk and appends
# a result line to summary.ndjson under flock.  Chunks with a DONE
# sentinel are skipped, so the driver is resumable (re-run with the same
# args after interruption).
#
# After the pool drains, totals.json is recomputed from summary.ndjson.
#
# Usage:
#   ./drive_incremental.sh OUT_ROOT [--scenarios "s1 s2 ..."] \
#                                  [--chunks N]   \
#                                  [--traces N]   \
#                                  [--depth D]    \
#                                  [--jobs J]
#
# Defaults:
#   scenarios = all 13
#   chunks    = 100
#   traces    = 1000 per chunk
#   depth     = 20   (auto-clamped to MAX_CLOCK-1 per scenario)
#   jobs      = max(1, $(nproc) - 2)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
INC_DIR="$(pwd)"

OUT_ROOT="${1:?usage: drive_incremental.sh OUT_ROOT [opts]}"
shift

SCENARIOS_DEFAULT=(amend_playground deep_book empty iceberg_resting mixed_tif
                   near_capacity one_sided_asks one_sided_bids
                   post_only_resting shallow_symmetric stacked_level
                   stops_pending stp_both_sides)
SCENARIOS=("${SCENARIOS_DEFAULT[@]}")
CHUNKS=100
TRACES=1000
DEPTH=20
JOBS=16  # 16 × Xmx2g ≈ 32 GB worst-case on a 91 GB host; 24 CPUs

while [[ $# -gt 0 ]]; do
    case "$1" in
        --scenarios) read -r -a SCENARIOS <<<"$2"; shift 2 ;;
        --chunks)    CHUNKS="$2"; shift 2 ;;
        --traces)    TRACES="$2"; shift 2 ;;
        --depth)     DEPTH="$2"; shift 2 ;;
        --jobs)      JOBS="$2"; shift 2 ;;
        *) echo "Unknown arg: $1" >&2; exit 1 ;;
    esac
done

mkdir -p "$OUT_ROOT"
SUMMARY="$OUT_ROOT/summary.ndjson"
TOTALS="$OUT_ROOT/totals.json"
touch "$SUMMARY"

cat <<EOF
=== Incremental TLC → C++ driver (parallel) ===
  Out root:    $OUT_ROOT
  Scenarios:   ${SCENARIOS[*]}
  Chunks each: $CHUNKS
  Traces/chk:  $TRACES
  Depth:       $DEPTH
  Parallel:    $JOBS workers
  Target:      $((${#SCENARIOS[@]} * CHUNKS * TRACES)) traces total
EOF

# Assemble job list: one line "scenario/chunk" per pending job.
# Workers skip jobs whose DONE sentinel already exists.
JOB_LIST=$(mktemp)
for scenario in "${SCENARIOS[@]}"; do
    for ((c = 0; c < CHUNKS; c++)); do
        [[ -f "$OUT_ROOT/$scenario/chunk_$c/DONE" ]] && continue
        echo "$scenario/$c"
    done
done > "$JOB_LIST"

N_JOBS=$(wc -l < "$JOB_LIST")
echo "  Pending:     $N_JOBS jobs"
echo

if (( N_JOBS == 0 )); then
    echo "Nothing to do (all chunks already DONE)."
    exit 0
fi

export OUT_ROOT TRACES DEPTH SUMMARY

# -P JOBS: parallel worker count
# -n 1:   one argument per worker invocation
# --line-buffered stdout so live tail sees progress.
xargs -a "$JOB_LIST" -n 1 -P "$JOBS" -I{} \
    bash -c '
        set -u
        arg="$1"
        echo "[$(date +%H:%M:%S)] start  $arg" >&2
        if "'"$INC_DIR"'/run_chunk.sh" "$arg"; then
            echo "[$(date +%H:%M:%S)] done   $arg" >&2
        else
            echo "[$(date +%H:%M:%S)] ERROR  $arg (exit $?)" >&2
        fi
    ' _ {} 2>&1 | cat

rm -f "$JOB_LIST"

# Recompute totals from summary.ndjson.
if [[ -s "$SUMMARY" ]]; then
    jq -s '{
        chunks: length,
        pass:            (map(.pass            // 0) | add),
        fail:            (map(.fail            // 0) | add),
        bug_divergences: (map(.bug_divergences // 0) | add),
        steps:           (map(.steps           // 0) | add)
    }' "$SUMMARY" > "$TOTALS"
else
    echo '{"chunks":0,"pass":0,"fail":0,"bug_divergences":0,"steps":0}' > "$TOTALS"
fi

echo "=== Done ==="
cat "$TOTALS"
