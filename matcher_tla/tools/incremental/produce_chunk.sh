#!/usr/bin/env bash
# produce_chunk.sh — run TLC -simulate for one scenario, one chunk.
#
# Writes N random-walk trace files into the chunk's raw directory.
# The chunk seed is derived from CHUNK_ID so different chunks produce
# independent random walks.
#
# Usage:
#   ./produce_chunk.sh SCENARIO CHUNK_ID N_TRACES DEPTH OUT_ROOT
#
# Outputs:
#   OUT_ROOT/<scenario>/chunk_<id>/raw/trace_<j>_<k>   (TLA+ text)
set -euo pipefail

SCENARIO="$1"
CHUNK_ID="$2"
N_TRACES="$3"
DEPTH="$4"
OUT_ROOT="$5"

TLA_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TLA_JAR="${TLA_JAR:-$HOME/tla-plus/tla2tools.jar}"
CFG="$TLA_DIR/${SCENARIO}__safety.cfg"
SPEC="MatchingEngine_${SCENARIO}"

if [[ ! -f "$CFG" ]]; then
    echo "Missing cfg: $CFG" >&2
    exit 1
fi
if [[ ! -f "$TLA_DIR/${SPEC}.tla" ]]; then
    echo "Missing spec: $TLA_DIR/${SPEC}.tla" >&2
    exit 1
fi

CHUNK_DIR="$OUT_ROOT/$SCENARIO/chunk_$CHUNK_ID"
RAW_DIR="$CHUNK_DIR/raw"
mkdir -p "$RAW_DIR"

# Seed derived from chunk id so chunks explore disjoint-ish walks.
SEED=$(( 1000003 * (CHUNK_ID + 1) + 7 ))

# TLC simulate only dumps walks that terminate within the depth bound;
# walks that reach the spec's MAX_CLOCK deadlock first and are discarded.
# Clamp DEPTH to MAX_CLOCK - 1 so every walk is dumpable.
MAX_CLOCK=$(awk '/MAX_CLOCK[[:space:]]*=/ {for(i=1;i<=NF;i++) if($i~/^[0-9]+$/){print $i;exit}}' "$CFG")
if [[ -n "${MAX_CLOCK:-}" ]] && (( DEPTH >= MAX_CLOCK )); then
    DEPTH=$(( MAX_CLOCK - 1 ))
fi

cd "$TLA_DIR"

# -simulate file=PREFIX,num=N writes PREFIX_0_0, PREFIX_0_1, ...
# -depth D caps each walk length.
# -deadlock disables deadlock reporting: scenarios that hit MAX_CLOCK
# before MAX_ORDERS have no enabled next-state transition from some
# reachable states; without this flag the first simulate walk to hit
# such a state errors out and no trace files are written.
# Each chunk gets its own -metadir. Two concurrent TLC invocations for
# the same scenario otherwise collide on the default metadir
# (./${SPEC}.tlc) and race on checkpoint/aril state files.
META_DIR="$CHUNK_DIR/tlc_meta"
mkdir -p "$META_DIR"

java -Xmx2g -Xss4m -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC \
    -workers 1 \
    -deadlock \
    -metadir "$META_DIR" \
    -simulate "file=$RAW_DIR/trace,num=$N_TRACES" \
    -depth "$DEPTH" \
    -seed "$SEED" \
    -config "$CFG" \
    "$SPEC" \
    > "$CHUNK_DIR/tlc.log" 2>&1 || true

rm -rf "$META_DIR"

# Count what we actually got; TLC may stop early on invariant violations.
N_FILES=$(ls "$RAW_DIR"/trace_* 2>/dev/null | wc -l)
echo "$N_FILES" > "$CHUNK_DIR/produced.count"
