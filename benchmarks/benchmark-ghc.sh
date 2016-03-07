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

cd "$1" || {
    echo "$0: Couldn't cd to '$1'" >> /dev/stderr
    exit 1
}

# Configure, with all required packages available
nix-shell -E "$(cabal2nix --shell ./.)" --run "cabal configure" || {
    echo "$0: Failed to configure '$1'" >> /dev/stderr
    exit 1
}

# Clean up the directory name
CLEAN=$(echo "$1" | tr -cd '[:alnum:]')
CACHE=$("$BASE/cacheDir.sh") || {
    echo "$0: Couldn't get cache dir" >> /dev/stderr
    exit 1
}

mkdir -p "$CACHE/benchmarks" || {
    echo "$0: Couldn't create benchmark directory" >> /dev/stderr
    exit 1
}

# Benchmark "cabal build"
BENCHMARK_COMMAND="cabal" \
BENCHMARK_ARGS='["build"]' \
BENCH_DIR="$CACHE/benchmarks" \
TIMING_NAME="cabal-build-$CLEAN" \
ENVIRONMENT_PACKAGES="" "$BASE/benchmarks/bench-run.sh"
