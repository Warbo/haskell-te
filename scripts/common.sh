#!/usr/bin/env bash

# Helper functions for scripts to source

function info {
    echo -e "INFO: $1" >> /dev/stderr
}

function warn {
    echo -e "WARNING: $1" >> /dev/stderr
    return 1
}

function abort {
    echo -e "ERROR: $1" >> /dev/stderr
    exit 1
}

function requireCmd {
    command -v "$1" > /dev/null || abort "$NAME needs $1"
}

function packageName {
    dump-package-name "$1" || abort "Couldn't get package name from '$1'"
}

function clusterNums {
    # The cluster parameters to use, one per line
    seq 1 3
}

function clusterCount {
    # The number of different cluster parameters to use
    clusterNums | wc -l
}

function findOutput {
    "$BASE/benchmarks/last-stdout.sh" > "$1.tmp" || {
        rm -f "$1.tmp"

        if [[ -f "$1" ]]
        then
            info "Using existing output"
        else
            abort "No stdout, aborting"
        fi
    }

    if [[ -f "$1.tmp" ]]
    then
        if [[ -f "$1" ]]
        then
            PREV_SIZE=$(du -k "$1" | cut -f1)
            NEW_SIZE=$(du -k "$1.tmp" | cut -f1)
            if [[ "$NEW_SIZE" -gt "$PREV_SIZE" ]]
            then
                rm -f "$1"
                mv "$1.tmp" "$1"
            else
                rm -f "$1.tmp"
            fi
        else
            mv "$1.tmp" "$1"
        fi
    fi
}

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
CACHE=$("$BASE/scripts/cacheDir.sh")
