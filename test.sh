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
    [[ -z "$DUPES" ]] || fail "mlspec made redundant lookups: $DUPES"
}

function mlspec {
    "$BASE/mlspec" < "$1" 2>&1
}

BASE=$(dirname "$(readlink -f "$0")")

for F in data/*
do
    echo "Exploring '$F'" >> /dev/stderr
    OUTPUT=$(mlspec "$F" | tee >(cat - >&5)) || fail "Failed to explore '$F'"
    echo "$OUTPUT" | noDupes
done
