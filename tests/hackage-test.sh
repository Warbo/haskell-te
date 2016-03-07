#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

function fail {
    echo -e "FAIL: $1" >> /dev/stderr
    exit 1
}

# Tests

function testShuffleShuffles {
    AMOUNT=$(( RANDOM % 100 + 10 ))
    CMD="$BASE/scripts/shufflePackages.sh"
    OUTPUT1=$("$CMD" | head -n$AMOUNT)
    OUTPUT2=$("$CMD" | head -n$AMOUNT)
    [[ "x$OUTPUT1" = "x$OUTPUT2" ]] &&
        fail "Calls to '$CMD' gave same output (up to line $AMOUNT):\n$OUTPUT1"
}

function testShuffleUnique {
    AMOUNT=$(( RANDOM % 100 + 10 ))
    CMD="$BASE/scripts/shufflePackages.sh"
    OUTPUT=$("$CMD" | head -n$AMOUNT) ||
        fail "Failed to run '$CMD'"
    RAW_COUNT=$(echo "$OUTPUT" | wc -l)
    UNIQUE=$(echo "$OUTPUT" | sort -u | wc -l)
    [[ "$RAW_COUNT" -eq "$UNIQUE" ]] ||
        fail "Only '$UNIQUE' unique lines in first '$AMOUNT' lines of '$CMD'"
}

# Test invocation

for TEST in testShuffleUnique testShuffleShuffles
do
    echo "Running '$TEST'"
    "$TEST"
done

echo "Hackage tests pass"
