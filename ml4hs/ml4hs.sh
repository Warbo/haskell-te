#!/usr/bin/env bash
set -e

for CMD in jq
do
    command -v "$CMD" > /dev/null || {
        echo "ml4hs.sh requires $CMD" 1>&2
        exit 1
    }
done

BASE=$(dirname "$(readlink -f "$0")")

"$BASE/format-exploration.sh" | "$BASE/run-exploration.sh"
