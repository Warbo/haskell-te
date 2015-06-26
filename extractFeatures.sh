#! /usr/bin/env nix-shell
#! nix-shell -p treefeatures -p bash -i bash

while read LINE
do
    NAME=$(echo "$LINE" | cut -d ' ' -f 1)
    AST=$(echo "$LINE" | cut -d ' ' -f 2-)
    FEATURES=$(echo "$AST" | BITS=30 MODE=sexpr TreeFeatures)
    echo "$NAME $FEATURES"
done
