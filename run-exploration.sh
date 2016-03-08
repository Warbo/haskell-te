#!/usr/bin/env bash

command -v MLSpec > /dev/null || {
    echo "run-exploration.sh requires MLSpec"
    exit 1
}

# shellcheck disable=SC2153
[[ -n "$CLUSTERS" ]] || {
    echo "run-exploration.sh needs CLUSTERS to be set" >> /dev/stderr
    exit 1
}

MLSpec
