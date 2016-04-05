#!/usr/bin/env bash

# Helper functions for scripts to source

function info {
    echo -e "INFO: $1" 1>&2
}

function warn {
    echo -e "WARNING: $1" 1>&2
    return 1
}

function abort {
    echo -e "ERROR: $1" 1>&2
    exit 1
}

function uniqueLines {
    mv "$1" "$1.tmp"
    sort -u < "$1.tmp" > "$1"
    rm -f "$1.tmp"
}

function requireCmd {
    command -v "$1" > /dev/null || abort "$NAME needs $1"
}

function clusterNums {
    # The cluster parameters to use, one per line
    seq 1 3
}

function clusterCount {
    # The number of different cluster parameters to use
    clusterNums | wc -l
}

function cacheDir {
    mktemp -d "haskell-te-XXXXX" || abort "Couldn't create temp dir $DIR"
}

function findOutput {
    "$BASE/benchmarks/last-stdout.sh" > "$1.tmp" || {
        rm -f "$1.tmp"

        [[ -f "$1" ]] || abort "No stdout, aborting"
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

function nonEmptyJson {
    [[ -f "$1" ]] || abort "Couldn't count JSON in non-existent '$1'"

    COUNT=$(jq 'length' < "$1") || abort "Failed to count JSON from '$1'"

    [[ "$COUNT" -gt 0 ]] || abort "JSON in '$1' is empty"
}

[[ -n "$BASE" ]] || abort "BASE needs to be set for common.sh"
CACHE=$(cacheDir)
mkdir -p "$CACHE/data"
