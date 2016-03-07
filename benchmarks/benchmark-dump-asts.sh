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

command -v cabal > /dev/null || {
    echo "'$0' requires cabal" >> /dev/stderr
    exit 1
}

command -v nix-shell > /dev/null || {
    echo "'$0' requires nix-shell" >> /dev/stderr
    exit 1
}

command -v cabal2nix > /dev/null || {
    echo "'$0' requires cabal2nix" >> /dev/stderr
    exit 1
}

command -v dump-package > /dev/null || {
    echo "'$0' requires dump-package" >> /dev/stderr
    exit 1
}

ENVIRONMENT_PACKAGES=""
BENCHMARK_COMMAND="runAstPlugin"

ESCAPED_ARG=$(echo "$1" | sed -e 's@\\"@\\\\"@g' | sed -e 's@"@\\"@g')
BENCHMARK_ARGS="[\"${ESCAPED_ARG}\"]"

CLEAN=$(echo "$1" | tr -cd '[:alnum:]')
CACHE=$("$BASE/cacheDir.sh") || {
    echo "$0: Couldn't get cache dir" >> /dev/stderr
    exit 1
}

BENCH_DIR="$CACHE/benchmarks"
mkdir -p "$BENCH_DIR" || {
    echo "$0: Couldn't create benchmark directory '$BENCH_DIR'" >> /dev/stderr
    exit 1
}

TIMING_NAME="dump-package-$CLEAN"

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
    export BENCHMARK_COMMAND
    export BENCHMARK_ARGS
    export BENCH_DIR
    export TIMING_NAME
    export ENVIRONMENT_PACKAGES
    nix-shell --show-trace -E "$ENV" --run "'$BASE/benchmarks/bench-run.sh'" || {
        echo "$0: Error benchmarking '$1'" >> /dev/stderr
        exit 1
    }
fi

echo "Looking for stdout" >> /dev/stderr

function upToDashes {
    while read -r LINE
    do
        if [[ "x$LINE" = "x-----" ]]
        then
            break
        else
            echo "$LINE"
        fi
    done
}

HAVE_OUTPUT=0
OUTPUT_FILE="$CACHE/$CLEAN.asts"
EXPECT=$(echo "$BENCHMARK_COMMAND $BENCHMARK_ARGS" | tr -dc '[:alnum:]')
echo "Expect: $EXPECT"
for F in "$BENCH_DIR"/outputs/*.stdout
do
    NAME=$(basename "$F" .stdout)
    FOUND=$(echo "$NAME" | tr -dc '[:alnum:]')
    echo "FOUND:  $FOUND"
    if [[ "x$FOUND" = "x$EXPECT" ]]
    then
        echo "Found stdout in '$F'" >> /dev/stderr
        HAVE_OUTPUT=1
        # Get everything following last occurrence of -----
        tac "$F" | upToDashes | tac > "$OUTPUT_FILE"
    fi
done

[[ "$HAVE_OUTPUT" -eq 1 ]] || {
    echo "Didn't find stdout, aborting" >> /dev/stderr
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
