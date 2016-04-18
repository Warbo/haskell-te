#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

function msg {
    echo "$1" 1>&2
}

function fail {
    msg "FAIL: $1"
    exit 1
}

function noDupes {
    DUPES=$(grep "^building path.*repo-head" |
            sed -e 's/.*head-//g'            |
            sort                             |
            uniq -D)
    [[ -z "$DUPES" ]] || fail "Made redundant package lookups: $DUPES"
}

function explore {
    "$BASE/explore-theories" < "$1" 2>&1
}

function testNoDupes {
    msg "Making sure packages aren't checked over and over"
    for F in data/*
    do
        msg "Exploring '$F'"
        OUTPUT=$(explore "$F") || fail "Failed to explore '$F'"
        echo "$OUTPUT" | noDupes
    done
    msg "No duplicate checks were spotted"
}

function testNoRegressions {
    OUTPUT=$(explore data/hastily.formatted.1) ||
        fail "Failed to explore 'hastily':\n$OUTPUT"
}

testNoDupes
testNoRegressions

echo "Tests passed (check prior output for more information)"
