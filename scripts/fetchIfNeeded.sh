#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

function findInCache {
    # Look through $CACHE for entries of the form $1-1.2.3
    for D in "$CACHE/packages"/*
    do
        if basename "$D" | grep "^$1-[0-9\.]*\$" > /dev/null
        then
            ABS=$(readlink -f "$D")
            echo "$ABS"
            return 0
        fi
    done
    return 1
}

[[ -n "$1" ]] || abort "$NAME requires a Hackage package name as argument"

PKG="$1"
mkdir -p "$CACHE/packages"

# See if we've previously failed to fetch this package
UNFETCHABLE="$CACHE/unfetchable"
touch "$UNFETCHABLE"
grep -Fx "$PKG" "$UNFETCHABLE" > /dev/null &&
    abort "Package '$PKG' is marked as unfetchable"

# See if we have a Hackage package already
FOUND=$(findInCache "$PKG") && {
    echo "$FOUND"
    exit 0
}

cd "$CACHE/packages" || abort "$NAME couldn't cd to '$CACHE/packages'"

cabal get "$1" 1>&2 || abort "Failed to download '$PKG' with Cabal"

FOUND=$(findInCache "$PKG") && {
    echo "$FOUND"
    exit 0
}

abort "Couldn't find '$PKG' after downloading it"
