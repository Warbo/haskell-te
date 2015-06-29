#!/usr/bin/env bash

# Main ML4HS script

# Check invocation
if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

NAMEDASTS=$(./dump-hackage.sh "$1")
FEATURES=$(echo "$NAMEDASTS" | ./extractFeatures.sh)
CLUSTERED=$(echo "$FEATURES" | ./cluster.sh)
LINEDUP=$(echo "$CLUSTERED" | ./lineUp.sh)

echo "$LINEDUP"
