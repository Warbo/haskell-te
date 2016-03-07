#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

for CMD in annotateDb
do
    command -v "$CMD" > /dev/null || abort "$NAME requires '$CMD'"
done

[[ -n "$1" ]] || abort "$NAME Needs a directory as argument"

[[ -d "$1" ]] || abort "$NAME couldn't find directory '$1'"

PKG=$(dump-package-name "$1") || abort "Couldn't get package name from '$1'"

CACHE=$("$BASE/cacheDir.sh")

ASTS="$CACHE/$PKG.asts"
[[ -f "$ASTS" ]] || abort "No ASTs found for '$PKG'"

BENCHMARK_COMMAND="annotateDb"
export BENCHMARK_COMMAND

BENCHMARK_ARGS="[\"${PKG}\"]"
export BENCHMARK_ARGS

TIMING_NAME="$BENCHMARK_COMMAND-$PKG"
export TIMING_NAME

ENVIRONMENT_PACKAGES=""
export ENVIRONMENT_PACKAGES

BENCH_DIR="$CACHE/benchmarks/annotate/$PKG"
export BENCH_DIR
mkdir -p "$BENCH_DIR"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    info "$NAME using existing result '$EXISTING'"
else
    "$BASE/benchmarks/bench-run.sh" < "$ASTS" ||
        abort "Failed to annotate ASTs for '$PKG'"
fi

OUTPUT_FILE="$CACHE/$PKG.annotated"

if [[ -f "$OUTPUT_FILE" ]]
then
    info "$NAME using existing '$OUTPUT_FILE'"
else
    "$BASE/benchmarks/last-stdout.sh" > "$OUTPUT_FILE" ||
        abort "$NAME found no stdout, aborting"

    [[ -f "$OUTPUT_FILE" ]] || abort "No such file '$OUTPUT_FILE'"
fi

AST_COUNT=$(jq 'length' < "$OUTPUT_FILE") ||
    abort "Failed to count outputted ASTs"

[[ "$AST_COUNT" -gt 0 ]] || abort "$NAME got no ASTs from '$1', abandoning"

info "Finished benchmarking annotatedb for '$1'"
