#!/usr/bin/env bash
# replay_chunk.sh — convert chunk's TLA traces to JSON, replay via C++
# conformance harness, record aggregate PASS/FAIL, delete raw artifacts.
#
# Usage:
#   ./replay_chunk.sh SCENARIO CHUNK_ID OUT_ROOT
#
# Inputs:
#   OUT_ROOT/<scenario>/chunk_<id>/raw/trace_*   (from produce_chunk.sh)
#
# Outputs:
#   OUT_ROOT/<scenario>/chunk_<id>/replay.log       (harness stdout+stderr)
#   OUT_ROOT/<scenario>/chunk_<id>/result.json      (per-chunk summary)
#   OUT_ROOT/<scenario>/chunk_<id>/DONE             (sentinel, replaces raw/+json/)
#
# After a successful replay the raw TLA traces and converted JSONs are
# deleted so disk use stays flat regardless of chunk count.
set -euo pipefail

SCENARIO="$1"
CHUNK_ID="$2"
OUT_ROOT="$3"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
CONVERTER="$REPO_ROOT/matcher_stl/tools/conformance/convert_matching_traces.py"
HARNESS="$REPO_ROOT/matcher_stl/build/conformance_harness"
SCENARIO_JSON="$REPO_ROOT/matcher_tla/scenarios/${SCENARIO}.json"

CHUNK_DIR="$OUT_ROOT/$SCENARIO/chunk_$CHUNK_ID"
RAW_DIR="$CHUNK_DIR/raw"
JSON_DIR="$CHUNK_DIR/json"

if [[ -f "$CHUNK_DIR/DONE" ]]; then
    # Already replayed; idempotent skip.
    exit 0
fi
if [[ ! -d "$RAW_DIR" ]]; then
    echo "No raw dir: $RAW_DIR" >&2
    exit 1
fi

N_RAW=$(ls "$RAW_DIR" 2>/dev/null | wc -l)
if (( N_RAW == 0 )); then
    echo '{"traces":0,"pass":0,"fail":0,"note":"no_traces"}' > "$CHUNK_DIR/result.json"
    rm -rf "$RAW_DIR"
    touch "$CHUNK_DIR/DONE"
    exit 0
fi

mkdir -p "$JSON_DIR"

# Convert every TLA text trace to JSON.  --simulate is the new flag for
# STATE_N == headers (see convert_matching_traces.py).
python3 "$CONVERTER" --simulate \
    --seed "$SCENARIO_JSON" \
    -o "$JSON_DIR" \
    "$RAW_DIR"/trace_* \
    > "$CHUNK_DIR/convert.log" 2>&1 || true

N_JSON=$(ls "$JSON_DIR"/*.json 2>/dev/null | wc -l)

if (( N_JSON == 0 )); then
    jq -n --argjson raw "$N_RAW" \
        '{traces: $raw, converted: 0, pass: 0, fail: 0, note: "all_empty_after_convert"}' \
        > "$CHUNK_DIR/result.json"
    rm -rf "$RAW_DIR" "$JSON_DIR"
    touch "$CHUNK_DIR/DONE"
    exit 0
fi

# Replay through the C++ harness.
"$HARNESS" "$JSON_DIR"/*.json > "$CHUNK_DIR/replay.log" 2>&1 || true

# Harness prints a final report with counts we can grep.
PASS=$(grep -oE '[0-9]+ passed'   "$CHUNK_DIR/replay.log" | head -1 | awk '{print $1}')
FAIL=$(grep -oE '[0-9]+ failed'   "$CHUNK_DIR/replay.log" | head -1 | awk '{print $1}')
BUGS=$(grep -oE 'BUG divergences:[[:space:]]+[0-9]+' "$CHUNK_DIR/replay.log" \
       | awk '{print $NF}')
STEPS=$(grep -oE 'Steps replayed:[[:space:]]+[0-9]+' "$CHUNK_DIR/replay.log" \
        | awk '{print $NF}')

PASS="${PASS:-0}"; FAIL="${FAIL:-0}"; BUGS="${BUGS:-0}"; STEPS="${STEPS:-0}"

jq -n \
    --arg scenario "$SCENARIO" \
    --argjson chunk "$CHUNK_ID" \
    --argjson raw  "$N_RAW" \
    --argjson json "$N_JSON" \
    --argjson pass  "$PASS" \
    --argjson fail  "$FAIL" \
    --argjson bugs  "$BUGS" \
    --argjson steps "$STEPS" \
    '{scenario:$scenario, chunk:$chunk, traces_raw:$raw, traces_json:$json,
      pass:$pass, fail:$fail, bug_divergences:$bugs, steps:$steps}' \
    > "$CHUNK_DIR/result.json"

# If anything diverged, keep the JSONs for investigation; otherwise wipe.
if (( FAIL > 0 || BUGS > 0 )); then
    mv "$JSON_DIR" "$CHUNK_DIR/json_failed"
else
    rm -rf "$JSON_DIR"
fi
rm -rf "$RAW_DIR"
touch "$CHUNK_DIR/DONE"
