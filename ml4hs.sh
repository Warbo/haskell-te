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

CLUSTERED=$(echo "$FEATURES" | ./cluster.sh | sort)

function lineUp {
    LINES=$(cat)
    # The first line is special, as it has no preceding space
    FIRST=$(echo "$LINES" | head -n 1)
    CLUSTER=$(echo "$FIRST" | cut -f 1)
    NAME=$(echo "$FIRST" | cut -f 2)
    printf "$NAME"
    # The rest of the lines are either " foo" or "\nfoo"
    echo "$LINES" | tail -n +2 | while read LINE
                                 do
                                     THISCLUSTER=$(echo "$LINE" | cut -f 1)
                                     THISNAME=$(echo "$LINE" | cut -f 2)
                                     if [[ "x$THISCLUSTER" = "x$CLUSTER" ]]
                                     then
                                         printf " $THISNAME"
                                     else
                                         printf "\n$THISNAME"
                                     fi
                                     CLUSTER="$THISCLUSTER"
                                 done
}

echo "$CLUSTERED" | lineUp
