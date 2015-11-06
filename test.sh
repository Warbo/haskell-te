#!/usr/bin/env bash

# Accumulate results, so we can repeat them after each package (to avoid
# trudging through compiler output)
RESULT=""

# Test each package we care about (dependencies will take care of themselves)
while read -r pkg
do
    RESULT="${RESULT}Testing $pkg: "
    if ./one.sh "$pkg"
    then
        RESULT="$RESULT PASS\n"
    else
        RESULT="$RESULT FAIL\n"
    fi
    echo -e "Results so far:\n$RESULT"
done < <(grep "call = " < default.nix | sed -e 's/^[ ]*\([^ ]*\).*/\1/g')
