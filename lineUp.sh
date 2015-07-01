#!/bin/sh

# Takes (sorted) input of the form:
#
# cluster1 foo
# cluster1 bar
# cluster2 baz
#
# Outputs each cluster as a separate line, eg.
#
# foo bar
# baz

LINES=$(cat)

# The first line is special, as it has no preceding space
FIRST=$(echo "$LINES"   | head -n 1)
CLUSTER=$(echo "$FIRST" | cut  -f 1)
NAME=$(echo "$FIRST"    | cut  -f 2)
printf "$NAME"

# The rest of the lines are either " foo" or "\nfoo"
echo "$LINES" | tail -n +2 | while read LINE
                             do
                                 THISCLUSTER=$(echo "$LINE" | cut -f 1)
                                 THISNAME=$(echo "$LINE"    | cut -f 2)
                                 # Start a new line if we've hit a new cluster
                                 if [[ "x$THISCLUSTER" = "x$CLUSTER" ]]
                                 then
                                     printf " $THISNAME"
                                 else
                                     printf "\n$THISNAME"
                                 fi
                                 CLUSTER="$THISCLUSTER"
                             done
