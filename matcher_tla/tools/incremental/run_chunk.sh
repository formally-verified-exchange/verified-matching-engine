#!/usr/bin/env bash
# run_chunk.sh — one worker-pool job: produce + replay one chunk.
#
# Invoked by drive_incremental.sh via xargs -P for parallel execution.
# Argument form (single xargs -n1 arg):  SCENARIO/CHUNK_ID
# Stdin-free: reads config from env vars set by the driver:
#   OUT_ROOT, TRACES, DEPTH, SUMMARY
set -euo pipefail
INC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

ARG="$1"
SCENARIO="${ARG%%/*}"
CHUNK_ID="${ARG##*/}"

CHUNK_DIR="$OUT_ROOT/$SCENARIO/chunk_$CHUNK_ID"
if [[ -f "$CHUNK_DIR/DONE" ]]; then
    exit 0
fi

"$INC_DIR/produce_chunk.sh" "$SCENARIO" "$CHUNK_ID" "$TRACES" "$DEPTH" "$OUT_ROOT"
"$INC_DIR/replay_chunk.sh"  "$SCENARIO" "$CHUNK_ID" "$OUT_ROOT"

if [[ -f "$CHUNK_DIR/result.json" ]]; then
    # Append one JSON line under flock so concurrent workers do not corrupt.
    (
        flock -x 9
        cat "$CHUNK_DIR/result.json" >> "$SUMMARY"
        echo >> "$SUMMARY"
    ) 9> "$SUMMARY.lock"
fi
