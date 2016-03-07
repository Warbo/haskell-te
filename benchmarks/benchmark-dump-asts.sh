#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

[[ -n "$1" ]] || {
    echo "'$0' requires a package directory" >> /dev/stderr
    exit 1
}

[[ -d "$1" ]] || {
    echo "'$0': Directory '$1' not found" >> /dev/stderr
    exit 1
}

cd "$1"

for CMD in cabal nix-shell cabal2nix dump-package
do
    command -v "$CMD" > /dev/null || {
        echo "'$0' requires dump-package" >> /dev/stderr
        exit 1
    }
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
CACHE=$("$BASE/cacheDir.sh") || {
    echo "$0: Couldn't get cache dir" >> /dev/stderr
    exit 1
}

BENCH_DIR="$CACHE/benchmarks"
export BENCH_DIR
mkdir -p "$BENCH_DIR" || {
    echo "$0: Couldn't create benchmark directory '$BENCH_DIR'" >> /dev/stderr
    exit 1
}

TIMING_NAME="$BENCHMARK_COMMAND-$CLEAN"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    echo "$0: Using existing result '$EXISTING'" >> /dev/stderr
else
    # We're essentially replicating the job of dump-package, since we'd like to
    # avoid measuring the time taken to build dependencies, etc.

    # Configure the package, using dump-haskell-env to ensure that AstPlugin is
    # available for GHC
    ENV=$(dump-package-env "$1") || {
        echo "Couldn't get Haskell package environment, aborting" >> /dev/stderr
        exit 1
    }
    nix-shell --show-trace -E "$ENV" --run "cabal configure" || {
        echo "Couldn't configure package, aborting" >> /dev/stderr
        exit 1
    }

    # Tell runAstPlugin not to configure the package itself
    SKIP_CABAL_CONFIG=1
    export SKIP_CABAL_CONFIG

    # Benchmark, inside the environment determined by dump-package-env
    export TIMING_NAME
    export ENVIRONMENT_PACKAGES
    nix-shell --show-trace -E "$ENV" --run "'$BASE/benchmarks/bench-run.sh'" || {
        echo "$0: Error benchmarking '$1'" >> /dev/stderr
        exit 1
    }
fi

echo "Looking for stdout" >> /dev/stderr
OUTPUT_FILE="$CACHE/$PKG.asts"

if [[ -f "$OUTPUT_FILE" ]]
then
    echo "Using existing '$OUTPUT_FILE'" >> /dev/stderr
else
    "$BASE/benchmarks/last-stdout.sh" > "$OUTPUT_FILE" || {
        echo "ERROR: No stdout, aborting" >> /dev/stderr
        exit 1
    }
    [[ -f "$OUTPUT_FILE" ]] || {
        echo "ERROR: No such file '$OUTPUT_FILE'" >> /dev/stderr
        exit 1
    }
fi

AST_COUNT=$(jq 'length' < "$OUTPUT_FILE") || {
    echo "ERROR: Failed to count outputted ASTs" >> /dev/stderr
    exit 1
}

[[ "$AST_COUNT" -gt 0 ]] || {
    echo "ERROR: Got no ASTs from '$1', abandoning" >> /dev/stderr
    exit 1
}

echo "Finished benchmark-dump-asts.sh" >> /dev/stderr
