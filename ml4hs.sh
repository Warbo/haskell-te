#!/usr/bin/env bash

# Main ML4HS script

shopt -s nullglob

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

# For some reason GHC only lets
LINES=$(./dump-hackage.sh "$1" 2>&1 1>/dev/null)
NAMEDASTS=$(echo "$LINES" | grep "^FOUNDAST" | cut -d ' ' -f 2-)

FEATURES=$(echo "$NAMEDASTS" | ./extractFeatures.sh)

echo "$FEATURES" | ./cluster.sh
