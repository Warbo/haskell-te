#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# shellcheck disable=SC2034
NAME=$(basename "$0")

# shellcheck source=../scripts/common.sh
source "$BASE/scripts/common.sh"

for CMD in build-env mlspec-bench
do
    requireCmd "$CMD"
done

[[ -n "$BENCHMARK_COMMAND" ]] || abort "Please provide a BENCHMARK_COMMAND"

[[ -n "$BENCH_DIR" ]] || abort "Please provide a BENCH_DIR variable"

[[ -d "$BENCH_DIR" ]] || abort "Given BENCH_DIR, '$BENCH_DIR', doesn't exist"

mkdir -p "$BENCH_DIR/outputs" || abort "Couldn't create '$BENCH_DIR/outputs'"

export BENCH_DIR

[[ -n "$TIMING_NAME" ]] || abort "Got no TIMING_NAME variable to name results"

OUTPUT="$BENCH_DIR/outputs/$TIMING_NAME.json"

# Check if we need to provide any input; to prevent waiting for user input
if [ -t 0 ]
then
    INPUT=""
else
    INPUT=$(cat)
fi

# We want to use Nix as little as possible inside our benchmarks, so we use
# build-env from explore-theories to provide all of the packages we'll need
info "Benchmarking '$BENCHMARK_COMMAND' with args '$BENCHMARK_ARGS'"
echo "$INPUT" | build-env mlspec-bench --template json --output "$OUTPUT" ||
    abort "Failed to benchmark, aborting"

[[ -z "$DELETE_BENCH_OUTPUT" ]] || {
    info "Deleting output directory '$BENCH_DIR'"
    rm -rf "$BENCH_DIR"
}
