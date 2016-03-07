#!/usr/bin/env bash

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

command -v dump-package > /dev/null || {
    echo "'$0' requires dump-package" >> /dev/stderr
    exit 1
}

ESCAPED_ARG=$(echo "$1" | sed -e 's@\\"@\\\\"@g' | sed -e 's@"@\\"@g')
BENCHMARK_ARGS="[\"${ESCAPED_ARG}\"]"
CLEAN=$(echo "$1" | tr -cd '[:alnum:]')
CACHE=$("$BASE/cacheDir.sh") || {
    echo "$0: Couldn't get cache dir" >> /dev/stderr
    exit 1
}

BENCH_DIR="$CACHE/benchmarks"
mkdir -p "$BENCH_DIR" || {
    echo "$0: Couldn't create benchmark directory '$BENCH_DIR'" >> /dev/stderr
    exit 1
}

BENCHMARK_COMMAND="dump-package"
TIMING_NAME="dump-package-$CLEAN"
ENVIRONMENT_PACKAGES=""

export BENCHMARK_COMMAND
export BENCHMARK_ARGS
export BENCH_DIR
export TIMING_NAME
export ENVIRONMENT_PACKAGES
"$BASE/benchmarks/bench-run.sh"
