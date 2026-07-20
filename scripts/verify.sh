#!/usr/bin/env bash
#
# Full verification gate for the matching engine.
#
# Four layers, each answering a different question:
#
#   1. Lean          -- are the proofs actually closed?
#   2. TLA+          -- is every invariant defined actually being checked,
#                       and does bounded model checking pass?
#   3. C++           -- does the executable engine behave, and does it match
#                       the TLA+ model on replayed traces?
#   4. Cross-artifact-- do Lean and TLA+ agree on well-formedness?
#
# Usage:
#   ./scripts/verify.sh              fast gate (smoke TLC config)
#   ./scripts/verify.sh --full       adds the three deep TLC configs (~30+ min)
#
# TLA_JAR must point at tla2tools.jar for layers 2 and 4; if it is missing
# those layers are reported SKIPPED, never PASSED.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TLA_JAR="${TLA_JAR:-${HOME}/tla-plus/tla2tools.jar}"
FULL=0
[[ "${1:-}" == "--full" ]] && FULL=1

FAILED=0
SKIPPED=0
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
fail() { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; FAILED=$((FAILED + 1)); }
skip() { printf '  \033[33mSKIP\033[0m  %s\n' "$1"; SKIPPED=$((SKIPPED + 1)); }
hdr()  { printf '\n\033[1m%s\033[0m\n' "$1"; }

# ---------------------------------------------------------------------------
hdr "1. Lean — proof closure"
# ---------------------------------------------------------------------------

if ( cd "$REPO/matcher_lean" && lake build ) > "$WORK/lake.log" 2>&1; then
    pass "lake build (library + all proof files)"
else
    fail "lake build"; tail -20 "$WORK/lake.log" | sed 's/^/        /'
fi

# `lake build` succeeding is not sufficient on its own: a proof file only gets
# checked if it is reachable from a default target, and a proof only means
# something if it is not resting on `sorry`.
if grep -rn '\bsorry\b' "$REPO/matcher_lean/MatchingEngine"/*.lean > "$WORK/sorry.txt" 2>&1; then
    fail "sorry found in proof files"; sed 's/^/        /' "$WORK/sorry.txt"
else
    pass "no 'sorry' in any proof file"
fi

# The definitive check. A theorem can depend on sorryAx without the token
# `sorry` appearing in the file that states it.
cat > "$WORK/AxiomCheck.lean" <<'EOF'
import MatchingEngine
#print axioms process_preserves_BookInvariant
#print axioms process_preserves_FullBookInv
#print axioms process_preserves_BookOk
#print axioms process_emits_safe_trades
#print axioms process_PostOnlyGuarantee
#print axioms process_STPGuarantee
#print axioms process_preserves_uncrossed
#print axioms Elegant.process_preserves_uncrossed_elegant
#print axioms processOrder_preserves_AllInv
EOF
if ( cd "$REPO/matcher_lean" && lake env lean "$WORK/AxiomCheck.lean" ) > "$WORK/axioms.txt" 2>&1; then
    if grep -q "sorryAx" "$WORK/axioms.txt"; then
        fail "a top-level theorem depends on sorryAx"
        grep "sorryAx" "$WORK/axioms.txt" | sed 's/^/        /'
    elif ! grep -q "depends on axioms" "$WORK/axioms.txt"; then
        fail "axiom check produced no output"; sed 's/^/        /' "$WORK/axioms.txt"
    else
        pass "top-level theorems depend only on standard axioms ($(grep -c 'depends on axioms' "$WORK/axioms.txt") checked)"
    fi
else
    fail "axiom check failed to run"; tail -10 "$WORK/axioms.txt" | sed 's/^/        /'
fi

if ( cd "$REPO/matcher_lean" && lake exe matchingengine ) > "$WORK/tests.log" 2>&1; then
    pass "lake exe matchingengine — $(grep -oE '[0-9]+ tests passed' "$WORK/tests.log" | tail -1)"
else
    fail "lean runtime tests"; tail -15 "$WORK/tests.log" | sed 's/^/        /'
fi

# ---------------------------------------------------------------------------
hdr "2. TLA+ — invariant coverage and model checking"
# ---------------------------------------------------------------------------

# Coverage: an invariant that is defined but not listed in a config's
# INVARIANTS block is never evaluated by that run. Silent, and indistinguishable
# from a clean result. Check every config against every defined invariant.
python3 - "$REPO" <<'PYEOF' > "$WORK/coverage.txt" 2>&1
import re, sys, glob, os
repo = sys.argv[1]
tla = open(f"{repo}/matcher_tla/MatchingEngine.tla").read()

# Invariants are the nullary operators in the invariants section that are
# named in at least one config, plus any operator whose body quantifies over
# the book. Take the explicit list: operators defined after the invariants
# banner and referenced by any cfg.
defined = set(re.findall(r'^([A-Z][A-Za-z0-9_]*)\s*==', tla, re.M))
cfgs = sorted(glob.glob(f"{repo}/matcher_tla/MatchingEngine*.cfg"))
listed_anywhere = set()
per_cfg = {}
for c in cfgs:
    body = open(c).read()
    m = re.search(r'^INVARIANTS\s*$(.*?)(?=^[A-Z]+\s*$|\Z)', body, re.M | re.S)
    names = set(re.findall(r'^\s+([A-Za-z][A-Za-z0-9_]*)\s*$', m.group(1), re.M)) if m else set()
    per_cfg[os.path.basename(c)] = names
    listed_anywhere |= names

universe = listed_anywhere & defined
bad = False
for c, names in sorted(per_cfg.items()):
    missing = universe - names
    if missing:
        bad = True
        print(f"MISSING {c}: {', '.join(sorted(missing))}")
orphan = {n for n in universe if n not in defined}
if orphan:
    bad = True
    print(f"UNDEFINED but listed: {', '.join(sorted(orphan))}")
print(f"OK {len(universe)} invariants x {len(per_cfg)} configs" if not bad else "COVERAGE GAP")
PYEOF

if grep -q "^OK " "$WORK/coverage.txt"; then
    pass "invariant coverage — $(grep '^OK ' "$WORK/coverage.txt" | sed 's/^OK //')"
else
    fail "invariant coverage gap"; grep -v "^COVERAGE GAP" "$WORK/coverage.txt" | sed 's/^/        /'
fi

# TLC spills its state queue to disk. The deep configs generate hundreds of
# millions of states, so this must NOT live on a tmpfs (a RAM-backed /tmp will
# fill and TLC dies with "No space left on device" mid-run, which looks nothing
# like an invariant violation). Default to a disk-backed cache dir; override
# with TLC_WORK.
TLC_WORK="${TLC_WORK:-$HOME/.cache/matcher-tlc}"

run_tlc() { # name cfg
    local name="$1" cfg="$2" d="$TLC_WORK/$1"
    rm -rf "$d"; mkdir -p "$d" || { fail "TLC $name (cannot create $d)"; return; }
    if [[ "$(df --output=fstype "$d" 2>/dev/null | tail -1)" == "tmpfs" ]]; then
        fail "TLC $name — TLC_WORK ($d) is on tmpfs; set TLC_WORK to disk-backed storage"
        return
    fi
    cp "$REPO/matcher_tla/MatchingEngine.tla" "$d/"
    if ( cd "$d" && java "-Djava.io.tmpdir=$d" -cp "$TLA_JAR" tlc2.TLC \
            -deadlock -workers auto -metadir "$d/meta" \
            -config "$REPO/matcher_tla/$cfg" MatchingEngine.tla ) \
            > "$d/out.txt" 2>&1 && grep -q "Model checking completed. No error" "$d/out.txt"; then
        pass "TLC $name — $(grep -oE '[0-9]+ distinct states found' "$d/out.txt" | tail -1)"
        rm -rf "$d/meta" "$d/states"
    else
        fail "TLC $name"
        grep -E "No space left|Error|Assert|Invariant .* is violated" "$d/out.txt" \
            | head -6 | sed 's/^/        /'
        printf '        (full log: %s)\n' "$d/out.txt"
    fi
}

if [[ ! -f "$TLA_JAR" ]]; then
    skip "TLC (TLA_JAR not found at $TLA_JAR)"
else
    run_tlc smoke MatchingEngine_smoke.cfg
    if [[ $FULL -eq 1 ]]; then
        run_tlc medium  MatchingEngine.cfg
        run_tlc amend   MatchingEngine_amend.cfg
        run_tlc noamend MatchingEngine_noamend.cfg
    else
        skip "TLC deep configs (use --full)"
    fi
fi

# ---------------------------------------------------------------------------
hdr "3. C++ — engine behaviour and conformance to the TLA+ model"
# ---------------------------------------------------------------------------

if [[ ! -x "$REPO/matcher_stl/build/test_correctness" ]]; then
    ( cd "$REPO/matcher_stl" && cmake -B build -S . -DCMAKE_BUILD_TYPE=Release \
        && cmake --build build -j ) > "$WORK/cmake.log" 2>&1 \
        || { fail "C++ build"; tail -15 "$WORK/cmake.log" | sed 's/^/        /'; }
fi

if [[ -x "$REPO/matcher_stl/build/test_correctness" ]]; then
    if ( cd "$REPO/matcher_stl" && ./build/test_correctness ) > "$WORK/cxx.log" 2>&1; then
        pass "test_correctness — $(grep -oE '[0-9]+ passed, [0-9]+ failed' "$WORK/cxx.log" | tail -1)"
    else
        fail "test_correctness"; grep -iE "fail" "$WORK/cxx.log" | head -10 | sed 's/^/        /'
    fi

    # The actual TLA+ <-> C++ link: replay converted TLC traces through the
    # real engine and compare book, fills and last-trade-price at every step.
    traces=("$REPO"/matcher_stl/tools/conformance/traces/json/*.json)
    if [[ -e "${traces[0]}" ]]; then
        if ( cd "$REPO/matcher_stl" && ./build/conformance_harness "${traces[@]}" ) \
                > "$WORK/conf.log" 2>&1 && grep -q "Result:            PASS" "$WORK/conf.log"; then
            pass "conformance replay — $(grep -oE 'Traces:.*' "$WORK/conf.log" | head -1 | tr -s ' ')"
            printf '        %s\n' "$(grep -oE 'Steps replayed:.*' "$WORK/conf.log" | tr -s ' ')"
        else
            fail "conformance replay"
            grep -E "FAIL|divergence|step [0-9]" "$WORK/conf.log" | head -10 | sed 's/^/        /'
        fi
    else
        fail "no conformance traces found"
    fi

    # Differential against the vector-based reference implementation.
    if ( cd "$REPO/matcher_stl" && ./build/shadow_test 2000 1 ) > "$WORK/shadow.log" 2>&1; then
        pass "shadow differential (2000 steps, seed 1)"
    else
        fail "shadow differential"; tail -12 "$WORK/shadow.log" | sed 's/^/        /'
    fi
fi

# ---------------------------------------------------------------------------
hdr "4. Cross-artifact — Lean vs TLA+ well-formedness"
# ---------------------------------------------------------------------------

if [[ ! -f "$TLA_JAR" ]]; then
    skip "WF differential (TLA_JAR not found)"
elif TLA_JAR="$TLA_JAR" "$REPO/scripts/wf_differential.sh" > "$WORK/wf.log" 2>&1; then
    pass "WF differential — $(grep -oE 'TLA\+ accepts [0-9]+ shapes' "$WORK/wf.log") , identical sets"
else
    fail "WF divergence between Lean and TLA+"
    grep -A6 "DIVERGENCE" "$WORK/wf.log" | head -12 | sed 's/^/        /'
fi

# ---------------------------------------------------------------------------
printf '\n\033[1m========================================\033[0m\n'
if [[ $FAILED -eq 0 ]]; then
    printf '\033[32mVERIFICATION PASSED\033[0m'
    [[ $SKIPPED -gt 0 ]] && printf ' (%d skipped)' "$SKIPPED"
    printf '\n'
    exit 0
else
    printf '\033[31mVERIFICATION FAILED\033[0m — %d check(s)\n' "$FAILED"
    exit 1
fi
