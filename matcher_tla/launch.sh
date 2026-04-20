#!/usr/bin/env bash
# launch.sh — detached launcher for run_experiments.sh
#
# Runs the experiment under nohup so it survives terminal close / laptop sleep,
# captures stdout+stderr to a timestamped log, records the PID, and prints
# commands for tailing progress and stopping cleanly.
#
# Usage:
#   ./launch.sh [fast|deep] [--timeout SEC] [--jobs N] [--phase A|B|all]
#
# Defaults: profile=deep (overnight-sized).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

PROFILE="${1:-deep}"
shift || true

case "$PROFILE" in
    fast|deep) ;;
    *) echo "profile must be 'fast' or 'deep'" >&2; exit 1 ;;
esac

OUT_DIR="experiments/$PROFILE"
mkdir -p "$OUT_DIR"

STAMP="$(date +%Y%m%d-%H%M%S)"
LOG="$OUT_DIR/launch.$STAMP.log"
PID_FILE="$OUT_DIR/launch.pid"

# Refuse to stomp a running instance — quick safety check.
if [[ -f "$PID_FILE" ]] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null; then
    echo "Already running: PID $(cat "$PID_FILE")" >&2
    echo "Stop it first with:  kill \$(cat $PID_FILE)" >&2
    exit 1
fi

# Detach. setsid + nohup so parent-shell death does not propagate a SIGHUP.
setsid nohup ./run_experiments.sh "$PROFILE" "$@" \
    > "$LOG" 2>&1 < /dev/null &
PID=$!
echo "$PID" > "$PID_FILE"

# Symlink "latest" for convenience.
ln -sfn "launch.$STAMP.log" "$OUT_DIR/launch.log"

cat <<EOF
Launched run_experiments.sh $PROFILE $*
  PID:      $PID
  Log:      $LOG
  Latest:   $OUT_DIR/launch.log (symlink)

Handy commands (run from $(pwd)):
  Tail:     tail -f $OUT_DIR/launch.log
  Status:   ./status.sh $PROFILE
  Stop:     kill \$(cat $PID_FILE)
EOF
