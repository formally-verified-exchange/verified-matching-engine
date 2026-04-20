#!/usr/bin/env bash
# run_experiments.sh — drive seeded TLC experiments end-to-end.
#
# Phase A (safety-only): for each scenario, run TLC with ONLY the real
#   safety invariants. No target. Any violation = a genuine model bug.
#
# Phase B (target-driven): for each (scenario, target) pair, run TLC to
#   force a counterexample trace, convert to JSON with the seed embedded,
#   then feed every trace through the C++ conformance harness.
#
# Usage:
#   ./run_experiments.sh fast [--phase A|B|all] [--jobs N] [--timeout SEC]
#   ./run_experiments.sh deep [--phase A|B|all] [--jobs N] [--timeout SEC]
#
# Defaults: profile=fast, phase=all, jobs=$(nproc)-2, timeout=1800s (30 min).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TLA_DIR="$REPO_ROOT/matcher_tla"
SCEN_DIR="$TLA_DIR/scenarios"
HARNESS_BIN="$REPO_ROOT/matcher_stl/build/conformance_harness"
CONVERTER="$REPO_ROOT/matcher_stl/tools/conformance/convert_matching_traces.py"
TLA_JAR="$HOME/tla-plus/tla2tools.jar"

PROFILE="${1:-fast}"
shift || true

PHASE="all"
JOBS="$(( $(nproc) - 2 ))"
[[ "$JOBS" -lt 1 ]] && JOBS=1
TIMEOUT="1800"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --phase)   PHASE="$2"; shift 2 ;;
        --jobs)    JOBS="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        *) echo "Unknown arg: $1" >&2; exit 1 ;;
    esac
done

if [[ "$PROFILE" != "fast" && "$PROFILE" != "deep" ]]; then
    echo "Profile must be 'fast' or 'deep'" >&2
    exit 1
fi

OUT_DIR="$TLA_DIR/experiments/$PROFILE"
RAW="$OUT_DIR/raw"
LOG="$OUT_DIR/log"
JSON="$OUT_DIR/json"
mkdir -p "$RAW" "$LOG" "$JSON"

echo "=== Setup ==="
echo "  Profile:       $PROFILE"
echo "  Phase:         $PHASE"
echo "  Jobs:          $JOBS"
echo "  Timeout/run:   ${TIMEOUT}s"
echo "  Out:           $OUT_DIR"
echo ""

# -------- (Re)generate all TLA modules + cfgs for this profile --------
echo "=== Regenerating TLA modules and cfgs (profile=$PROFILE) ==="
python3 "$SCEN_DIR/gen_seeded.py" "$SCEN_DIR"/*.json --profile "$PROFILE" >/dev/null
echo "  done."
echo ""

# -------- Worker: run one TLC invocation against a single cfg --------
# Invoked by xargs. Writes raw TLC output to $RAW/<tag>.txt and a short
# summary line to $LOG/<tag>.status.
run_tlc() {
    local cfg="$1"
    local tag
    tag="$(basename "$cfg" .cfg)"
    local scenario="${tag%%__*}"
    local kind="${tag#${scenario}__}"
    local raw="$RAW/$tag.txt"
    local status="$LOG/$tag.status"

    # Per-run metadir AND per-run java.io.tmpdir: TLC otherwise collides on
    # two things when run in parallel:
    #   1. states/<timestamp>/ metadir (one per second granularity)
    #   2. stdlib extraction (Integers.tla, TLC.tla, etc.) into the system
    #      /tmp — concurrent extracts race and one worker sees a partial file.
    local metadir="$OUT_DIR/tlc_meta/$tag"
    local jtmp="$OUT_DIR/jtmp/$tag"
    mkdir -p "$metadir" "$jtmp"
    (
        cd "$TLA_DIR"
        timeout --preserve-status "$TIMEOUT" \
            java "-Djava.io.tmpdir=$jtmp" -cp "$TLA_JAR" tlc2.TLC \
                -deadlock -config "$cfg" -workers 1 \
                -metadir "$metadir" \
                "MatchingEngine_${scenario}.tla" \
                >"$raw" 2>&1
    ) || true

    local exit_line
    # TLC writes either a success or a violation. We classify by grep.
    if grep -q 'Error: Invariant .* is violated' "$raw"; then
        local inv
        inv=$(grep -m1 'Error: Invariant' "$raw" | sed 's/.*Invariant \([^ ]*\).*/\1/')
        echo "VIOLATED $tag invariant=$inv" >"$status"
    elif grep -q 'Model checking completed.' "$raw" \
         || grep -q 'states generated' "$raw"; then
        echo "PASS $tag" >"$status"
    else
        echo "ERROR $tag" >"$status"
    fi
}
export -f run_tlc
export TIMEOUT TLA_JAR TLA_DIR RAW LOG OUT_DIR

# -------- Phase A: safety-only --------
phase_A() {
    echo "=== Phase A — safety-only TLC ==="
    local cfgs
    mapfile -t cfgs < <(ls "$TLA_DIR"/*__safety.cfg 2>/dev/null | sort)
    echo "  scenarios: ${#cfgs[@]}"
    printf '%s\n' "${cfgs[@]}" | xargs -I{} -P "$JOBS" bash -c 'run_tlc "$@"' _ {}

    local pass=0 viol=0 err=0
    for s in "$LOG"/*__safety.status; do
        [[ -f "$s" ]] || continue
        case "$(cat "$s")" in
            PASS*)     pass=$((pass+1)) ;;
            VIOLATED*) viol=$((viol+1)) ;;
            ERROR*)    err=$((err+1)) ;;
        esac
    done
    echo ""
    echo "  PASS:     $pass"
    echo "  VIOLATED: $viol  <-- any violation here is a real model bug"
    echo "  ERROR:    $err   (timeout/exec error; check raw logs)"
    if (( viol > 0 )); then
        echo ""
        echo "  Violations (full trace in $RAW/<tag>.txt):"
        for s in "$LOG"/*__safety.status; do
            grep -q '^VIOLATED' "$s" && cat "$s" | sed 's/^/    /'
        done
    fi
    echo ""
    return 0
}

# -------- Phase B: target-driven + C++ replay --------
phase_B() {
    echo "=== Phase B — target-driven TLC + C++ conformance ==="
    local cfgs
    mapfile -t cfgs < <(ls "$TLA_DIR"/*__Target*.cfg 2>/dev/null | sort)
    echo "  cfgs: ${#cfgs[@]}"
    printf '%s\n' "${cfgs[@]}" | xargs -I{} -P "$JOBS" bash -c 'run_tlc "$@"' _ {}

    # Convert every raw TLC trace that produced a counterexample into JSON.
    # Each cfg's corresponding scenario JSON is the seed source.
    echo ""
    echo "  Converting traces to JSON..."
    local converted=0 skipped=0
    for s in "$LOG"/*__Target*.status; do
        [[ -f "$s" ]] || continue
        local tag; tag="$(basename "$s" .status)"
        local scenario="${tag%%__*}"
        local raw="$RAW/$tag.txt"
        local out="$JSON/$tag.json"
        if grep -q '^VIOLATED' "$s"; then
            python3 "$CONVERTER" "$raw" \
                --seed "$SCEN_DIR/$scenario.json" \
                > "$out" 2>/dev/null
            converted=$((converted+1))
        else
            skipped=$((skipped+1))
        fi
    done
    echo "    converted: $converted"
    echo "    skipped (no violation → no trace): $skipped"

    # Run C++ conformance harness on all converted traces.
    if (( converted == 0 )); then
        echo "  No traces to replay."
        return 0
    fi
    if [[ ! -x "$HARNESS_BIN" ]]; then
        echo "  Harness not built at $HARNESS_BIN — build matcher_stl first." >&2
        return 1
    fi
    echo ""
    echo "  Running conformance harness on $converted traces..."
    "$HARNESS_BIN" "$JSON"/*.json | tee "$OUT_DIR/harness_report.txt"
    echo ""
}

case "$PHASE" in
    A)   phase_A ;;
    B)   phase_B ;;
    all) phase_A; phase_B ;;
    *) echo "phase must be A, B, or all" >&2; exit 1 ;;
esac

echo "=== Done. Artifacts in: $OUT_DIR ==="
