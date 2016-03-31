#!/usr/bin/env bash
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# shellcheck source=common.sh
source "$BASE/scripts/common.sh"

EXISTING="$BENCH_DIR/outputs/$TIMING_NAME.json"
if [[ -f "$EXISTING" ]]
then
    info "Using existing result '$EXISTING'"
    exit 0
fi

exit 1
