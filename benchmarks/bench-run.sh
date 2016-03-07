#!/usr/bin/env bash

command -v build-env > /dev/null || {
    echo "bench-run.sh requires build-env" >> /dev/stderr
    exit 1
}

command -v mlspec-bench > /dev/null || {
    echo "bench-run.sh requires mlspec-bench" >> /dev/stderr
    exit 1
}

[[ -z "$BENCHMARK_COMMAND" ]] && {
    echo "Please provide a BENCHMARK_COMMAND variable" >> /dev/stderr
    exit 1
}

[[ -z "$BENCH_DIR" ]] && {
    echo "Please provide a BENCH_DIR variable" >> /dev/stderr
    exit 1
}

[[ -d "$BENCH_DIR" ]] || {
    echo "Given BENCH_DIR, '$BENCH_DIR', doesn't exist" >> /dev/stderr
    exit 1
}

mkdir -p "$BENCH_DIR/outputs" || {
    echo "Couldn't create '$BENCH_DIR/outputs', aborting" >> /dev/stderr
    exit 1
}

echo "Results will be written to '$BENCH_DIR/outputs'" >> /dev/stderr
export BENCH_DIR

[[ -z "$TIMING_NAME" ]] && {
    echo "Please provide a TIMING_NAME variable, to name the generated files" >> /dev/stderr
    exit 1
}

OUTPUT="$BENCH_DIR/outputs/$TIMING_NAME.json"

if [[ -z "$ENVIRONMENT_PACKAGES" ]]
then
    echo "INFO: No ENVIRONMENT_PACKAGES given" >> /dev/stderr
fi

# Check if we need to provide any input; to prevent waiting for user input
if [ -t 0 ]
then
    echo "No stdin given, using empty string" >> /dev/stderr
    INPUT=""
else
    echo "Using stdin as given" >> /dev/stderr
    INPUT=$(cat)
fi

# We want to use Nix as little as possible inside our benchmarks, so we use
# build-env from explore-theories to provide all of the packages we'll need
echo "Benchmarking '$BENCHMARK_COMMAND' with args '$BENCHMARK_ARGS'" >> /dev/stderr
echo "$INPUT" | build-env mlspec-bench --template json --output "$OUTPUT" || {
    echo "$0: Failed to benchmark, aborting" >> /dev/stderr
    exit 1
}

[[ -z "$DELETE_BENCH_OUTPUT" ]] || {
    echo "Deleting output directory '$BENCH_DIR'" >> /dev/stderr
    rm -rf "$BENCH_DIR"
}
