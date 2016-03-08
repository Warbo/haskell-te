#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
source "$BASE/scripts/common.sh"

TIME_FILE="$CACHE/$BENCHMARK_COMMAND.time"
TIME_CMD=$(command -v time)
"$TIME_CMD" -f '%e' -o "$TIME_FILE" \
            "$BENCHMARK_COMMAND" 1> "$BENCH_DIR/outputs/$BENCHMARK_COMMAND.stdout" \
                                 2> "$BENCH_DIR/outputs/$BENCHMARK_COMMAND.stderr"
TIME_USED=$(cat "$TIME_FILE")
echo "TIME USED: $TIME_USED"
echo "[{\"reportAnalysis\":{\"anMean\":{\"estPoint\":$TIME_USED}}}]" > "$BENCH_DIR/outputs/$TIMING_NAME.json"
