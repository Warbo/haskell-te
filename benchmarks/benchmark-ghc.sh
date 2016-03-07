#!/usr/bin/env bash

# Benchmark regular building with Cabal + GHC

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

[[ -n "$1" ]] || {
    echo "'$0' requires a package directory" >> /dev/stderr
    exit 1
}

[[ -d "$1" ]] || {
    echo "'$0': Directory '$1' not found" >> /dev/stderr
    exit 1
}

command -v cabal > /dev/null || {
    echo "'$0' requires cabal" >> /dev/stderr
    exit 1
}

command -v nix-shell > /dev/null || {
    echo "'$0' requires nix-shell" >> /dev/stderr
    exit 1
}

command -v cabal2nix > /dev/null || {
    echo "'$0' requires cabal2nix" >> /dev/stderr
    exit 1
}

# See if we've already benchmarked this package
CACHE=$("$BASE/cacheDir.sh") || {
    echo "$0: Couldn't get cache dir" >> /dev/stderr
    exit 1
}

UNBUILDABLE="$CACHE/unbuildable"
touch "$UNBUILDABLE"
if grep -Fx "$1" "$UNBUILDABLE" > /dev/null
then
    echo "$0: Package '$1' is marked as unbuildable, aborting" >> /dev/stderr
    exit 1
fi

CLEAN=$(echo "$1" | tr -cd '[:alnum:]')
TIMING_NAME="cabal-build-$CLEAN"

BENCH_DIR="$CACHE/benchmarks"
mkdir -p "$BENCH_DIR" || {
    echo "$0: Couldn't create benchmark directory '$BENCH_DIR'" >> /dev/stderr
    exit 1
}

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    echo "$0: Using existing result '$EXISTING'" >> /dev/stderr
    exit 0
fi

# Configure, with all required packages available
cd "$1" || {
    echo "$0: Couldn't cd to '$1'" >> /dev/stderr
    exit 1
}

nix-shell --show-trace -E "$(cabal2nix --shell ./.)" --run "cabal configure" || {
    echo "$0: Failed to configure '$1'" >> /dev/stderr
    exit 1
}

# Benchmark "cabal build"
BENCHMARK_COMMAND="cabal"
BENCHMARK_ARGS='["build"]'
ENVIRONMENT_PACKAGES=""

export BENCHMARK_COMMAND
export BENCHMARK_ARGS
export TIMING_NAME
export BENCH_DIR
export ENVIRONMENT_PACKAGES
"$BASE/benchmarks/bench-run.sh"
