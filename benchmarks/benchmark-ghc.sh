#!/usr/bin/env bash

# Benchmark regular building with Cabal + GHC

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

[[ -n "$1" ]] || abort "$NAME requires a package directory"

[[ -d "$1" ]] || abort "$NAME couldn't find directory '$1'"

for CMD in cabal nix-shell cabal2nix
do
    command -v "$CMD" > /dev/null || abort "$NAME requires $CMD"
done

# See if we've already benchmarked this package
CACHE=$("$BASE/cacheDir.sh") || abort "$NAME couldn't get cache dir"

UNBUILDABLE="$CACHE/unbuildable"
touch "$UNBUILDABLE"
grep -Fx "$1" "$UNBUILDABLE" > /dev/null &&
    abort "Package '$1' is marked as unbuildable"

CLEAN=$(echo "$1" | tr -cd '[:alnum:]')
TIMING_NAME="cabal-build-$CLEAN"

BENCH_DIR="$CACHE/benchmarks"
mkdir -p "$BENCH_DIR" ||
    abort "$NAME couldn't create benchmark directory '$BENCH_DIR'"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    info "$NAME using existing result '$EXISTING'" >> /dev/stderr
    exit 0
fi

# Configure, with all required packages available
cd "$1" || abort "$NAME couldn't cd to '$1'"

nix-shell --show-trace -E "$(cabal2nix --shell ./.)" --run "cabal configure" ||
    abort "$NAME failed to configure '$1'"

# Benchmark "cabal build"
BENCHMARK_COMMAND="cabal"
BENCHMARK_ARGS='["build"]'
ENVIRONMENT_PACKAGES=""

export BENCHMARK_COMMAND
export BENCHMARK_ARGS
export TIMING_NAME
export BENCH_DIR
export ENVIRONMENT_PACKAGES
"$BASE/benchmarks/bench-run.sh" || abort "Failed to benchmark GHC for '$1'"

info "Finished benchmarking GHC for '$1'"
