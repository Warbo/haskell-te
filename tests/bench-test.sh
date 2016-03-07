#!/usr/bin/env bash

ERR=0
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# Tests for benchmarking commands

function testBenchTrue {
    BENCHMARK_COMMAND=true TIMING_NAME=true mlspecBench ||
        fail "Couldn't benchmark the 'true' command"
}

function testBenchCompile {
    for PKG in list-extras xmonad
    do
        # Only fetch if we can't already find it
        FOUND=$("$BASE/fetchIfNeeded.sh" "$PKG") || fail "Couldn't fetch '$PKG'"

        OUTPUT=$("$BASE/benchmarks/benchmark-ghc.sh" "$FOUND") || {
            fail "Problem benchmarking GHC in '$FOUND'"
            continue
        }

        if echo "$OUTPUT" | grep " exited with code " > /dev/null
        then
            fail "Cabal build failed for '$PKG':\n$OUTPUT"
            continue
        fi
    done
}

# Helpers

function nixPath {
    "$BASE/nix-support/nixPath.sh"
}

function mlspecBench {
    NIX_PATH="$(nixPath)" "$BASE/benchmarks/bench-run.sh"
}

function fail {
    echo -e "FAIL: $1" >> /dev/stderr
    ERR=1
    return 1
}

function findPkgSrc {
    for D in "$BENCH_DIR"/*
    do
        NAME=$(basename "$D")
        if echo "$NAME" | grep "^$1-[0-9\.]*$" > /dev/null
        then
            echo "Using existing '$NAME' for '$1'" >> /dev/stderr
            readlink -f "$D"
            return 0
        fi
    done
    return 1
}

# Test invocation

BENCH_DIR="$PWD/test-data"
export BENCH_DIR
mkdir -p "$BENCH_DIR/outputs"

testBenchTrue
testBenchCompile

exit "$ERR"
