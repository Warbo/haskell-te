#!/bin/sh

RESULT=""

# Test each package we care about (dependencies will take care of themselves)
for pkg in hipspecifyer hipspec treefeatures hs2ast ml4hs
do
    RESULT="${RESULT}Testing $pkg: "
    if nix-shell \
           -p "(import ./. {}).$pkg" \
           --command 'true' \
           --show-trace
    then
        RESULT="$RESULT PASS\n"
    else
        RESULT="$RESULT FAIL\n"
    fi
    echo -e "Results so far:\n$RESULT"
done
