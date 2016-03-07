#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")

for CMD in annotateDb
do
    command -v "$CMD" > /dev/null || {
        echo "ERROR: benchmark-annotate.sh requires '$CMD'" >> /dev/stderr
        exit 1
    }
done

[[ -n "$1" ]] || {
    echo "ERROR: $NAME Needs a directory as argument" >> /dev/stderr
    exit 1
}

[[ -d "$1" ]] || {
    echo "ERROR: Directory '$1' not found" >> /dev/stderr
    exit 1
}

PKG=$(dump-package-name "$1") || {
    echo "ERROR: Couldn't get package name from '$1'" >> /dev/stderr
    exit 1
}

CACHE=$("$BASE/cacheDir.sh")

ASTS="$CACHE/$PKG.asts"
[[ -f "$ASTS" ]] || {
    echo "ERROR: No ASTs found for '$PKG'" >> /dev/stderr
    exit 1
}

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
    echo "$0: Using existing result '$EXISTING'" >> /dev/stderr
else
    "$BASE/benchmarks/bench-run.sh" < "$ASTS" || {
        echo "Failed to annotate ASTs for '$PKG'" >> /dev/stderr
        exit 1
    }
fi

OUTPUT_FILE="$CACHE/$PKG.annotated"
"$BASE/benchmarks/last-stdout.sh" > "$OUTPUT_FILE"  || {
    echo "No stdout, aborting" >> /dev/stderr
    exit 1
}

[[ -f "$OUTPUT_FILE" ]] || {
    echo "Didn't copy stdout, aborting" >> /dev/stderr
    exit 1
}

AST_COUNT=$(jq 'length' < "$OUTPUT_FILE") || {
    echo "Failed to count outputted ASTs" >> /dev/stderr
    exit 1
}

[[ "$AST_COUNT" -gt 0 ]] || {
    echo "Got no ASTs from '$1', abandoning" >> /dev/stderr
    exit 1
}
