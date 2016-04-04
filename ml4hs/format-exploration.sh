#!/usr/bin/env bash

command -v jq > /dev/null || {
    echo "format-exploration.sh requires jq" 1>&2
    exit 1
}

# shellcheck disable=SC2153
[[ -n "$CLUSTERS" ]] || {
    echo "format-exploration.sh needs CLUSTERS to be set" 1>&2
    exit 1
}

INPUT=$(cat)

function individualClusters {
    # shellcheck disable=SC2153
    for CLUSTER in $(seq 1 "$CLUSTERS")
    do
        # Select entries which have a "cluster" attribute matching $CLUSTER, a
        # non-null "type" attribute and a true "quickspecable" attribute.
        GOT=$(echo "$INPUT" | jq -c \
            "map(select(.cluster == $CLUSTER and .type != null and .quickspecable))")

        # Only output non-empty clusters
        LENGTH=$(echo "$GOT" | jq 'length')
        if [[ "$LENGTH" -gt 0 ]]
        then
            echo "$GOT"
        fi
    done
}

# Put each cluster in an array
individualClusters | jq -s '.'
