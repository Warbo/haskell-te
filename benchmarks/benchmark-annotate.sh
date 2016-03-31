#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")

# shellcheck source=../scripts/common.sh
source "$BASE/scripts/common.sh"

requireCmd annotateDb

[[ -n "$1" ]] || abort "$NAME Needs a directory as argument"

[[ -d "$1" ]] || abort "$NAME couldn't find directory '$1'"

PKG=$(dump-package-name "$1") || abort "Couldn't get package name from '$1'"

ASTS="$CACHE/data/$PKG.asts"

nonEmptyJson "$ASTS"

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

"$BASE/scripts/runBenchmark.sh" < "$ASTS" || abort "Error benchmarking"

info "Looking for stdout"
OUTPUT_FILE="$CACHE/data/$PKG.annotated"

findOutput "$OUTPUT_FILE"

nonEmptyJson "$OUTPUT_FILE"

USABLE=$(jq 'map(.quickspecable and .type != null) | any' < "$OUTPUT_FILE")

[[ "x$USABLE" = "xtrue" ]] || {
    echo "$PKG" >> "$CACHE/unquickspecable"
    uniqueLines "$CACHE/unquickspecable"
    abort "$PKG gave no quickspecable definitions"
}

info "Finished benchmarking annotatedb for '$1'"
