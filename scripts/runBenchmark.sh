#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
source "$BASE/scripts/common.sh"

mkdir -p "$BENCH_DIR/outputs"

function chooseMethod {
    if [[ -n "$QUICK" ]]
    then
        CACHE="$CACHE" "$BASE/scripts/quickTime.sh" ||
            abort "Failed to quick benchmark '$BENCHMARK_COMMAND'"
    else
        "$BASE/benchmarks/bench-run.sh" ||
            abort "Failed to benchmark '$BENCHMARK_COMMAND'"
    fi
}

if ! "$BASE/scripts/skipBenchmark.sh"
then
    chooseMethod
fi
