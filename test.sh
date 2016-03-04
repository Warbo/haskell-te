#!/usr/bin/env bash

# Run everything in tests/

BASE=$(dirname "$(readlink "$0")")
[[ -d "$BASE/tests" ]] || {
    echo "Couldn't find '$BASE/tests' directory" >> /dev/stderr
    exit 1
}

for T in "$BASE/tests"/*
do
    "$T" || {
        echo "Tests '$T' failed" >> /dev/stderr
        exit 1
    }
done

echo "Tests passed"
