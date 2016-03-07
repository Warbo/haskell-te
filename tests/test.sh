#!/usr/bin/env bash

# Run everything in tests/

BASE=$(dirname "$(dirname "$(readlink "$0")")")
source "$BASE/scripts/common.sh"

[[ -d "$BASE/tests" ]] || abort "Couldn't find '$BASE/tests' directory"

for T in "$BASE/tests"/*-test.sh
do
    "$T" || abort "Tests '$T' failed"
done

echo "Tests passed"
