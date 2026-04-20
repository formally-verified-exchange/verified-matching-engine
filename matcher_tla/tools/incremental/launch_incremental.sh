#!/usr/bin/env bash
# launch_incremental.sh — detached launcher for drive_incremental.sh.
#
# Runs the driver under nohup so it survives terminal close, logs to a
# timestamped file, and records the PID.
#
# Usage:
#   ./launch_incremental.sh OUT_ROOT [driver args...]
#
# Example:
#   ./launch_incremental.sh experiments/inc --chunks 50 --traces 500 --depth 15
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

OUT_ROOT="${1:?usage: launch_incremental.sh OUT_ROOT [driver opts]}"
shift
mkdir -p "$OUT_ROOT"

STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="$OUT_ROOT/launch.$STAMP.log"
PID_FILE="$OUT_ROOT/launch.pid"

if [[ -f "$PID_FILE" ]] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null; then
    echo "Already running: PID $(cat "$PID_FILE")" >&2
    exit 1
fi

setsid nohup ./drive_incremental.sh "$OUT_ROOT" "$@" \
    > "$LOG" 2>&1 < /dev/null &
PID=$!
echo "$PID" > "$PID_FILE"
ln -sfn "launch.$STAMP.log" "$OUT_ROOT/launch.log"

cat <<EOF
Launched drive_incremental.sh
  PID:      $PID
  Log:      $LOG
  Latest:   $OUT_ROOT/launch.log
  Tail:     tail -f $OUT_ROOT/launch.log
  Totals:   cat $OUT_ROOT/totals.json   (updated after each chunk)
  Stop:     kill \$(cat $PID_FILE)
EOF
