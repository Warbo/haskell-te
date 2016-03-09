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

TIME_FILE="$CACHE/$BENCHMARK_COMMAND.time"
TIME_CMD=$(command -v time)
"$TIME_CMD" -f '%e' -o "$TIME_FILE" \
            "$BENCHMARK_COMMAND" "${ARGARRAY[@]}" \
            1> "$BENCH_DIR/outputs/$BENCHMARK_COMMAND.stdout" \
            2> "$BENCH_DIR/outputs/$BENCHMARK_COMMAND.stderr" ||
    abort "Failure when benchmarking '$BENCHMARK_COMMAND' on '$BENCHMARK_ARGS'"

TIME_USED=$(cat "$TIME_FILE")
echo "TIME USED: $TIME_USED"

RESULT="$BENCH_DIR/outputs/$TIMING_NAME.json"
echo "[{\"reportAnalysis\":{\"anMean\":{\"estPoint\":$TIME_USED}}}]" > "$RESULT"

jq '.' < "$RESULT" > /dev/null || {
    warn "Deleting unparseable benchmark result '$RESULT'"
    rm -f "$RESULT"
}
