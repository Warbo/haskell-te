#!/usr/bin/env bash

ERR=0
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# shellcheck source=../scripts/common.sh
source "$BASE/scripts/common.sh"

# Tests for benchmarking commands

function testBenchTrue {
    BENCHMARK_COMMAND=true TIMING_NAME=true mlspecBench ||
        fail "Couldn't benchmark the 'true' command"
}

function testBenchCompile {
    for PKG in list-extras xmonad
    do
        FOUND=$("$BASE/scripts/fetchIfNeeded.sh" "$PKG") ||
            fail "Couldn't fetch '$PKG'"

        info "Fetched '$FOUND' for '$PKG'"

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
    "$BASE/benchmarks/bench-run.sh"
}

function fail {
    echo -e "FAIL: $1" >> /dev/stderr
    ERR=1
    return 1
}

# Test invocation

BENCH_DIR="$CACHE/test-data"
export BENCH_DIR
mkdir -p "$BENCH_DIR/outputs"

testBenchTrue
testBenchCompile

exit "$ERR"
