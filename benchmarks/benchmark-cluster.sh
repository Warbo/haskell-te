#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")

# shellcheck source=../scripts/common.sh
source "$BASE/scripts/common.sh"

requireCmd cluster

# Get the annotated ASTs associated with the given source directory
[[ -n "$1" ]] || abort "$NAME needs a package directory as first argument"

PKG=$(packageName "$1")

# Set the number of clusters given in our argument
[[ -n "$2" ]] || abort "$NAME needs a cluster number as second argument"

CLUSTERS="$2"
export CLUSTERS

ANNOTATED="$CACHE/data/$PKG.annotated"

nonEmptyJson "$ANNOTATED"

# Set the benchmark parameters

BENCHMARK_COMMAND="cluster"
export BENCHMARK_COMMAND

BENCHMARK_ARGS="[]"
export BENCHMARK_ARGS

TIMING_NAME="$BENCHMARK_COMMAND-$PKG-$CLUSTERS"
export TIMING_NAME

BENCH_DIR="$CACHE/benchmarks/cluster/$PKG/$CLUSTERS-clusters"
export BENCH_DIR

"$BASE/scripts/runBenchmark.sh" < "$ANNOTATED" || abort "Error benchmarking"

info "Looking for stdout"
OUTPUT_FILE="$CACHE/data/$PKG.clustered.$CLUSTERS"

findOutput "$OUTPUT_FILE"

nonEmptyJson "$OUTPUT_FILE"

info "Finished benchmark-cluster.sh"
