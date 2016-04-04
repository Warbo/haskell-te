#!/usr/bin/env bash

command -v MLSpec > /dev/null || {
    echo "run-exploration.sh requires MLSpec" 1>&2
    exit 2
}

# shellcheck disable=SC2153
[[ -n "$CLUSTERS" ]] || {
    echo "run-exploration.sh needs CLUSTERS to be set" 1>&2
    exit 3
}

MLSpec
