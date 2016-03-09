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

function uniqueLines {
    mv "$1" "$1.tmp"
    sort -u < "$1.tmp" > "$1"
    rm -f "$1.tmp"
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

function cacheDir {
    if [[ -w "$BASE" ]]
    then
        # If we can write to the same place as our scripts, do so as it allows
        # committing files for reproducibility
        DIR="$BASE/cache"
        mkdir -p "$DIR" 1>&2 || abort "Couldn't create dir '$DIR'"
    elif [[ -n "$XDG_CACHE_HOME" ]] && [[ -d "$XDG_CACHE_HOME" ]]
    then
        # On many systems, 'mktemp -d' will use an in-memory filesystem, which will
        # quickly fill up. To avoid that, we try to use XDG_CACHE_HOME instead.
        DIR="$XDG_CACHE_HOME/haskell-te"
        mkdir -p "$DIR" 1>&2 || abort "Couldn't create dir '$DIR'"
    elif [[ -n "$HOME" ]] && [[ -d "$HOME" ]]
    then
        # If $HOME exists, try falling back to the recommended ~/.cache directory
        DIR="$HOME/.cache/haskell-te"
        mkdir -p "$DIR" 1>&2 || abort "Couldn't create dir '$DIR'"
    else
        # If $HOME doesn't exist, we're probably a daemon. Use mktemp, in the hope
        # that it's sane.
        DIR=$(mktemp -d "haskell-te") || abort "Couldn't create temp dir $DIR"
    fi
    echo "$DIR"
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

info "Sourcing common.sh from $0"

[[ -n "$BASE" ]] || abort "BASE needs to be set for common.sh"
CACHE=$(cacheDir)
mkdir -p "$CACHE/data"
