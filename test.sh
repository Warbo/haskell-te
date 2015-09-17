#!/bin/sh

RESULT=""

# Test each package we care about (dependencies will take care of themselves)
for FILE in components/*.rev.nix
do
    pkg=$(basename "$FILE" .rev.nix)
    RESULT="${RESULT}Testing $pkg: "
    if ./one.sh "$pkg"
    then
        RESULT="$RESULT PASS\n"
    else
        RESULT="$RESULT FAIL\n"
    fi
    echo -e "Results so far:\n$RESULT"
done
