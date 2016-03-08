#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

[[ -n "$1" ]] || abort "$NAME requires a package directory"

[[ -d "$1" ]] || abort "Directory '$1' not found"

cd "$1"

for CMD in cabal nix-shell cabal2nix dump-package
do
    requireCmd "$CMD"
done

PKG=$(dump-package-name "$1")

ENVIRONMENT_PACKAGES=""
export ENVIRONMENT_PACKAGES

BENCHMARK_COMMAND="runAstPlugin"
export BENCHMARK_COMMAND

ESCAPED_ARG=$(echo "$1" | sed -e 's@\\"@\\\\"@g' | sed -e 's@"@\\"@g')
BENCHMARK_ARGS="[\"${ESCAPED_ARG}\"]"
export BENCHMARK_ARGS

CLEAN=$(echo "$PKG" | tr -cd '[:alnum:]')

BENCH_DIR="$CACHE/benchmarks"
export BENCH_DIR
mkdir -p "$BENCH_DIR" ||
    abort "$NAME couldn't create benchmark directory '$BENCH_DIR'"

TIMING_NAME="$BENCHMARK_COMMAND-$CLEAN"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    info "$NAME using existing result '$EXISTING'"
else
    # We're essentially replicating the job of dump-package, since we'd like to
    # avoid measuring the time taken to build dependencies, etc.

    # Configure the package, using dump-haskell-env to ensure that AstPlugin is
    # available for GHC
    ENV=$(dump-package-env "$1") ||
        abort "Couldn't get Haskell package environment"

    nix-shell --show-trace -E "$ENV" --run "cabal configure" ||
        abort "Couldn't configure package"

    # Tell runAstPlugin not to configure the package itself
    SKIP_CABAL_CONFIG=1
    export SKIP_CABAL_CONFIG

    # Benchmark, inside the environment determined by dump-package-env
    export TIMING_NAME
    export ENVIRONMENT_PACKAGES
    nix-shell --show-trace -E "$ENV" --run "'$BASE/benchmarks/bench-run.sh'" ||
        abort "$NAME couldn't benchmark '$1'"
fi

info "Looking for stdout"
OUTPUT_FILE="$CACHE/data/$PKG.asts"

if [[ -f "$OUTPUT_FILE" ]]
then
    info "Using existing '$OUTPUT_FILE'"
else
    "$BASE/benchmarks/last-stdout.sh" > "$OUTPUT_FILE" ||
        abort "No stdout, aborting"

    [[ -f "$OUTPUT_FILE" ]] || abort "No such file '$OUTPUT_FILE'"
fi

AST_COUNT=$(jq 'length' < "$OUTPUT_FILE") ||
    abort "Failed to count outputted ASTs"

[[ "$AST_COUNT" -gt 0 ]] || abort "Got no ASTs from '$1'"

info "$NAME finished"
