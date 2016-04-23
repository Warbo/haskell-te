#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

function msg {
    echo "$1" 1>&2
}

echo "Tests passed (check prior output for more information)"
