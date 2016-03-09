#!/usr/bin/env bash

command -v jq > /dev/null || {
    echo "format-exploration.sh requires jq" >> /dev/stderr
    exit 1
}

# shellcheck disable=SC2153
[[ -n "$CLUSTERS" ]] || {
    echo "format-exploration.sh needs CLUSTERS to be set" >> /dev/stderr
    exit 1
}

INPUT=$(cat)

function individualClusters {
    # shellcheck disable=SC2153
    for CLUSTER in $(seq 1 "$CLUSTERS")
    do
        echo "$INPUT" | jq -c "map(select(.cluster == $CLUSTER and .quickspecable))"
    done
}

# Put each cluster in an array
individualClusters | jq -s '.'
