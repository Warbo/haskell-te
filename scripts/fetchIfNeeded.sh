#!/usr/bin/env bash

function findInCache {
    # Look through the contents of $2 for entries of the form $1-1.2.3
    for D in "$2"/*
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


BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

[[ -n "$1" ]] || {
    echo "$0: Requires a Hackage package name as argument" >> /dev/stderr
    exit 1
}

PKG="$1"
DIR=$("$BASE/cacheDir.sh")

# See if we've previously failed to fetch this package
UNFETCHABLE="$DIR/unfetchable"
touch "$UNFETCHABLE"
if grep -Fx "$PKG" "$UNFETCHABLE" > /dev/null
then
    echo "$0: Package '$PKG' is marked as unfetchable, aborting" >> /dev/stderr
    exit 1
fi

# See if we have a Hackage package already
FOUND=$(findInCache "$PKG" "$DIR") && {
    echo "Using cached version '$FOUND' for '$PKG'" >> /dev/stderr
    echo "$FOUND"
    exit 0
}

echo "No cached version of '$PKG' found, downloading with Cabal" >> /dev/stderr
cd "$DIR" || {
    echo "$0: Couldn't cd to '$DIR', aborting" >> /dev/stderr
    exit 1
}

cabal get "$1" 1>&2 || {
    echo "Failed to download '$PKG' with Cabal, aborting" >> /dev/stderr
    exit 1
}

FOUND=$(findInCache "$PKG" "$DIR") && {
    echo "Using '$FOUND' for '$PKG'" >> /dev/stderr
    echo "$FOUND"
    exit 0
}

echo "$0: Couldn't find '$PKG' after downloading it; aborting" >> /dev/stderr
exit 1
