#! /usr/bin/env nix-shell
#! nix-shell -i bash -p mlspec bash

# shellcheck disable=SC2153
[[ -n "$CLUSTERS" ]] || {
    echo "run-exploration.sh needs CLUSTERS to be set" >> /dev/stderr
    exit 1
}

MLSpec
