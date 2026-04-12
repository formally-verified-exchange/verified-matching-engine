#!/bin/bash
set -e

TLC="java -cp $HOME/tla-plus/tla2tools.jar tlc2.TLC"
SPEC="MatchingEngine.tla"
cd "$(dirname "$0")"

CONFIGS=(
    "MatchingEngine.cfg:Medium (2 orders, 3 prices, no amend)"
    "MatchingEngine_amend.cfg:With Amend (2 orders, 2 prices)"
    "MatchingEngine_noamend.cfg:3-order (3 orders, 2 prices, no amend)"
)

PASS=0
FAIL=0

for entry in "${CONFIGS[@]}"; do
    cfg="${entry%%:*}"
    label="${entry##*:}"
    echo "============================================================"
    echo "  $label"
    echo "  Config: $cfg"
    echo "============================================================"
    if $TLC -deadlock -config "$cfg" -workers auto "$SPEC" 2>&1; then
        echo ">>> PASS: $label"
        ((PASS++))
    else
        echo ">>> FAIL: $label"
        ((FAIL++))
    fi
    echo
done

echo "============================================================"
echo "  Summary: $PASS passed, $FAIL failed (out of ${#CONFIGS[@]})"
echo "============================================================"

[ "$FAIL" -eq 0 ]
