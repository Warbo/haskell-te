#!/usr/bin/env bash

# Benchmark regular building with Cabal + GHC

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

[[ -n "$1" ]] || abort "$NAME requires a package directory"

[[ -d "$1" ]] || abort "$NAME couldn't find directory '$1'"

for CMD in cabal nix-shell cabal2nix
do
    requireCmd "$CMD"
done

# See if we've already benchmarked this package
UNBUILDABLE="$CACHE/unbuildable"
touch "$UNBUILDABLE"
grep -Fx "$1" "$UNBUILDABLE" > /dev/null &&
    abort "Package '$1' is marked as unbuildable"

PKG=$(packageName "$1")

BENCHMARK_COMMAND="cabal"
export BENCHMARK_COMMAND

BENCHMARK_ARGS='["build"]'
export BENCHMARK_ARGS

TIMING_NAME="cabal-build-$PKG"
export TIMING_NAME

BENCH_DIR="$CACHE/benchmarks/ghc/$PKG"
export BENCH_DIR

ENVIRONMENT_PACKAGES=""
export ENVIRONMENT_PACKAGES

if "$BASE/scripts/skipBenchmark.sh"
then
    # We can exit right away, since our build products aren't needed
    exit 0
fi

# Configure, with all required packages available
cd "$1" || abort "$NAME couldn't cd to '$1'"

nix-shell --show-trace -E "$(cabal2nix --shell ./.)" --run "cabal configure" ||
    abort "$NAME failed to configure '$1'"

"$BASE/scripts/runBenchmark.sh"

info "Finished benchmarking GHC for '$1'"
