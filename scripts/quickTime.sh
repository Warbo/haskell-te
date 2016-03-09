#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
source "$BASE/scripts/common.sh"

# Turn our arguments into an array, if we have any
if [[ "x$BENCHMARK_ARGS" = "x[]" ]]
then
    ARGARRAY=()
else
    # Use jq to parse arguments into something bash-compatible
    eval "ARGARRAY=( $(echo "$BENCHMARK_ARGS" | jq -r '@sh') )"
fi

info "Quick benchmarking '$BENCHMARK_COMMAND' '${ARGARRAY[@]}'"

CLEAN_ARGS=$(echo "$BENCHMARK_ARGS" | tr -dc '[:alnum:]')

# This isn't quite the same as mlspec-bench would give. We're stripping out
# non-alphanumeric characters, whilst mlspec-bench replaces them with
# underscores.
# For the sake of compatibility, we shouldn't look for particular filenames.
# Instead, each benchmark should have a different BENCH_DIR, e.g.
#   BENCH_DIR="$CACHE/benchmarks/cluster/aeson/3-clusters"
# Then we can simply grab *.stdout, *.stderr and *.json
OUT_NAME="$BENCH_DIR/outputs/${BENCHMARK_COMMAND}_${CLEAN_ARGS}"

mkdir -p "$(dirname "$OUT_NAME")"

TIME_FILE="$CACHE/$BENCHMARK_COMMAND.time"
TIME_CMD=$(command -v time)

# Run the 'time' command, storing only the %elapsed time into TIME_FILE.
# The command we're timing is BENCHMARK_COMMAND, given arguments BENCHMARK_ARGS
# (via conversion to ARGARRAY to account for quoting, whitespace, etc.)
# If we have any stdin, it will be sent to BENCHMARK_COMMAND automatically. The
# stdout of BENCHMARK_COMMAND will be stored in OUT_NAME.stdout, and its stderr
# in OUT_NAME.stderr.

"$TIME_CMD" -f '%e' -o "$TIME_FILE" \
            "$BENCHMARK_COMMAND" "${ARGARRAY[@]}" \
                                 1> "$OUT_NAME.stdout" \
                                 2> "$OUT_NAME.stderr" || {
    cat "$OUT_NAME.stderr" >> /dev/stderr
    abort "Failure when benchmarking '$BENCHMARK_COMMAND' on '$BENCHMARK_ARGS'"
}

TIME_USED=$(cat "$TIME_FILE")
echo "TIME USED: $TIME_USED"

RESULT="$BENCH_DIR/outputs/$TIMING_NAME.json"
echo "[{\"reportAnalysis\":{\"anMean\":{\"estPoint\":$TIME_USED}}}]" > "$RESULT"

jq '.' < "$RESULT" > /dev/null || {
    warn "Deleting unparseable benchmark result '$RESULT'"
    rm -f "$RESULT"
}
