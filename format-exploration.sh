#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq bash

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
        echo "$INPUT" | jq -c "map(select(.cluster == $CLUSTER))"
    done
}

# Put each cluster in an array
individualClusters | jq -s '.'
