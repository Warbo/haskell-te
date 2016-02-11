#!/usr/bin/env bash

# Make a copy of stdout, to allow captured output to be displayed in real time
exec 5>&1-

function fail {
    echo "FAIL: $1" >> /dev/stderr
    exit 1
}

function noDupes {
    DUPES=$(grep "^building path.*repo-head" |
            sed -e 's/.*head-//g'            |
            sort                             |
            uniq -D)
    [[ -z "$DUPES" ]] || fail "'$CMD' made redundant lookups: $DUPES"
}

function explore {
    "$CMD" < "$1" 2>&1
}

BASE=$(dirname "$(readlink -f "$0")")
CMD="$BASE/explore-theories"

for F in data/*
do
    echo "Exploring '$F'" >> /dev/stderr
    OUTPUT=$(explore "$F" | tee >(cat - >&5)) || # tee gives us realtime output
        fail "Failed to explore '$F'"
    echo "$OUTPUT" | noDupes
done
