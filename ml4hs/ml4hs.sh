#!/usr/bin/env bash
set -e

command -v jq > /dev/null || {
    echo "ml4hs.sh requires jq" 1>&2
    exit 1
}

BASE=$(dirname "$(readlink -f "$0")")

"$BASE/format-exploration.sh" | "$BASE/run-exploration.sh"
