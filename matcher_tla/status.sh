#!/usr/bin/env bash
# status.sh — quick-look progress report for a running (or finished) experiment.
#
# Usage:   ./status.sh [fast|deep]   (default: deep)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

PROFILE="${1:-deep}"
OUT="experiments/$PROFILE"
LOG_DIR="$OUT/log"
PID_FILE="$OUT/launch.pid"

if [[ ! -d "$OUT" ]]; then
    echo "No experiment dir: $OUT"
    exit 0
fi

# Main orchestrator process state.
if [[ -f "$PID_FILE" ]] && kill -0 "$(cat "$PID_FILE")" 2>/dev/null; then
    PID="$(cat "$PID_FILE")"
    ETIME="$(ps -o etime= -p "$PID" | tr -d ' ')"
    RUN_STATE="RUNNING (PID $PID, elapsed $ETIME)"
else
    RUN_STATE="STOPPED"
fi

# cfg counts by kind.
cfg_total=$(ls *__*.cfg 2>/dev/null | wc -l)
cfg_safety=$(ls *__safety.cfg 2>/dev/null | wc -l)
cfg_target=$(( cfg_total - cfg_safety ))

# Status counts (completed runs).
pass=0; viol=0; err=0
if [[ -d "$LOG_DIR" ]]; then
    for s in "$LOG_DIR"/*.status; do
        [[ -f "$s" ]] || continue
        case "$(awk '{print $1}' "$s")" in
            PASS)     pass=$((pass+1)) ;;
            VIOLATED) viol=$((viol+1)) ;;
            ERROR)    err=$((err+1)) ;;
        esac
    done
fi
done=$(( pass + viol + err ))

printf 'Profile:    %s\n' "$PROFILE"
printf 'Out dir:    %s\n' "$OUT"
printf 'Launcher:   %s\n' "$RUN_STATE"
printf 'Progress:   %d / %d cfgs   (safety=%d  target=%d)\n' \
    "$done" "$cfg_total" "$cfg_safety" "$cfg_target"
printf '  PASS:       %d\n' "$pass"
printf '  VIOLATED:   %d   <-- real model bugs if in Phase A, expected in Phase B\n' "$viol"
printf '  ERROR:      %d   (timeouts / parse errors — inspect raw/)\n' "$err"

# Phase A specifically.
a_pass=0; a_viol=0; a_err=0
if [[ -d "$LOG_DIR" ]]; then
    for s in "$LOG_DIR"/*__safety.status; do
        [[ -f "$s" ]] || continue
        case "$(awk '{print $1}' "$s")" in
            PASS) a_pass=$((a_pass+1)) ;;
            VIOLATED) a_viol=$((a_viol+1)) ;;
            ERROR) a_err=$((a_err+1)) ;;
        esac
    done
fi
printf 'Phase A:    %d PASS | %d VIOLATED | %d ERROR   (out of %d scenarios)\n' \
    "$a_pass" "$a_viol" "$a_err" "$cfg_safety"

# Any Phase A violation = real bug, surface the scenario.
if (( a_viol > 0 )); then
    printf '\n*** Phase A violations ***\n'
    for s in "$LOG_DIR"/*__safety.status; do
        [[ -f "$s" ]] || continue
        if grep -q '^VIOLATED' "$s"; then
            cat "$s" | sed 's/^/  /'
        fi
    done
fi

# Currently running TLC workers.
tlc_running=$(pgrep -af 'tlc2.TLC' | wc -l)
printf '\nActive TLC workers: %d\n' "$tlc_running"
if (( tlc_running > 0 )); then
    pgrep -af 'tlc2.TLC' | awk '{ for (i=1;i<=NF;i++) if ($i=="-config") { print "  " $(i+1); break } }' | head -8
fi

# Final result line if orchestrator finished.
if [[ "$RUN_STATE" == "STOPPED" && -f "$OUT/harness_report.txt" ]]; then
    printf '\nHarness report tail:\n'
    tail -12 "$OUT/harness_report.txt" | sed 's/^/  /'
fi
