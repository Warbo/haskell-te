#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
CACHE=$("$BASE/scripts/cacheDir.sh")

function fail {
    echo -e "ERROR: $1" >> /dev/stderr
    exit 1
}

for CMD in cluster
do
    command -v "$CMD" > /dev/null || fail "$NAME needs '$CMD'"
done

# Get the annotated ASTs associated with the given source directory
[[ -n "$1" ]] || fail "$NAME needs a package directory as first argument"

PKG=$(dump-package-name "$1") || fail "Couldn't get package name from '$1'"

ANNOTATED="$CACHE/$PKG.annotated"
[[ -f "$ANNOTATED" ]] || fail "No ASTs found for '$PKG'"

# Set the number of clusters given in our argument
[[ -n "$2" ]] || fail "$NAME needs a cluster number as second argument"

CLUSTERS="$2"
export CLUSTERS

# Set the benchmark parameters

BENCHMARK_COMMAND="cluster"
export BENCHMARK_COMMAND

BENCHMARK_ARGS="[]"
export BENCHMARK_ARGS

TIMING_NAME="$BENCHMARK_COMMAND-$PKG-$CLUSTERS"
export TIMING_NAME

BENCH_DIR="$CACHE/benchmarks/cluster/$PKG/$CLUSTERS-clusters"
export BENCH_DIR
mkdir -p "$BENCH_DIR"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    echo "$NAME: Using existing result '$EXISTING'" >> /dev/stderr
else
    "$BASE/benchmarks/bench-run.sh" < "$ANNOTATED" ||
        fail "Failed to cluster '$PKG' into '$CLUSTERS'"
fi

echo "Looking for stdout" >> /dev/stderr
OUTPUT_FILE="$CACHE/$PKG.clustered.$CLUSTERS"

if [[ -f "$OUTPUT_FILE" ]]
then
    echo "Using existing '$OUTPUT_FILE'" >> /dev/stderr
else
    "$BASE/benchmarks/last-stdout.sh" > "$OUTPUT_FILE" ||
        fail "No stdout, aborting"

    [[ -f "$OUTPUT_FILE" ]] ||
        fail "No such file '$OUTPUT_FILE'"
fi

AST_COUNT=$(jq 'length' < "$OUTPUT_FILE") ||
    fail "Failed to count outputted ASTs"

[[ "$AST_COUNT" -gt 0 ]] || fail "Got no clusters from '$1', abandoning"

echo "Finished benchmark-cluster.sh" >> /dev/stderr
