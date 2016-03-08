#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

for CMD in dump-package-name ml4hs
do
    requireCmd "$CMD"
done

# Get the clusters associated with the given source directory
[[ -n "$1" ]] || abort "$NAME needs a package directory as first argument"

PKG=$(packageName "$1")

# Set the number of clusters given in our argument
[[ -n "$2" ]] || abort "$NAME needs a cluster number as second argument"

CLUSTERS="$2"
export CLUSTERS

# Find the clusters which should have been made by benchmark-cluster.sh
CLUSTERED="$CACHE/$PKG.clustered.$CLUSTERS"
[[ -f "$CLUSTERED" ]] || abort "Couldn't find '$PKG' clustered into '$CLUSTERS'"

# TODO: Adjust the format slightly for MLSpec
FORMATTED="$CACHE/$PKG.formatted.$CLUSTERS"

FORMATTER="$(dirname "$(dirname "$(command -v ml4hs)")")/lib/ml4hs/format-exploration.sh"
[[ -f "$FORMATTER" ]] || abort "Couldn't find format-exploration.sh at '$FORMATTER'"

"$FORMATTER" < "$CLUSTERED" > "$FORMATTED"

# Set the benchmark parameters

BENCHMARK_COMMAND="explore-theories"
export BENCHMARK_COMMAND

BENCHMARK_ARGS="[]"
export BENCHMARK_ARGS

TIMING_NAME="$BENCHMARK_COMMAND-$PKG-$CLUSTERS"
export TIMING_NAME

BENCH_DIR="$CACHE/benchmarks/explore/$PKG/$CLUSTERS-clusters"
export BENCH_DIR

"$BASE/scripts/runBenchmark.sh" < "$FORMATTED"

info "Looking for stdout"
OUTPUT_FILE="$CACHE/data/$PKG.explored.$CLUSTERS"

findOutput "$OUTPUT_FILE"

echo "Finished benchmark-explore.sh" >> /dev/stderr
