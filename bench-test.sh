#! /usr/bin/env nix-shell
#! nix-shell -i bash -p explore-theories bash

ERR=0
BASE=$(dirname "$(readlink -f "$0")")

# Tests for benchmarking commands

function testBenchTrue {
    BENCHMARK_COMMAND=true TIMING_NAME=true mlspec-bench ||
        fail "Couldn't benchmark the 'true' command"
}

function testBenchCompile {
    for PKG in list-extras xmonad
    do
        if FOUND=$(findPkgSrc "$PKG")
        then
            true
        else
            echo "Fetching '$PKG'" >> /dev/stderr
            pushd "$BENCH_DIR" > /dev/null
            cabal get "$PKG"
            popd > /dev/null
            FOUND=$(findPkgSrc "$PKG") || {
                fail "Couldn't find source for '$PKG'" >> /dev/stderr
                return 1
            }
        fi
        pushd "$FOUND" > /dev/null
        echo "Configuring '$PKG'" >> /dev/stderr
        OUTPUT=$(nix-shell -E "$(cabal2nix --shell ./.)" --run "cabal configure" 2>&1) || {
            fail "Problem configuring '$PKG': $OUTPUT"
            popd > /dev/null
            return 1
        }
        TIMING_NAME="compile_$PKG" BENCHMARK_COMMAND="cabal build"  mlspec-bench
        popd > /dev/null
        exit
    done
}

# Helpers

function fail {
    echo "FAIL: $1" >> /dev/stderr
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

function mlspec-bench {
    bash "$BASE/run.sh"
}

# Test invocation

BENCH_DIR="$PWD/test-data"
export BENCH_DIR
mkdir -p "$BENCH_DIR/outputs"

#testBenchTrue
testBenchCompile

exit "$ERR"
