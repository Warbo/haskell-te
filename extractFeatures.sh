#! /usr/bin/env nix-shell
#! nix-shell -p treefeatures -p bash -i bash

while read LINE
do
    PREFIX=$(echo "$LINE" | cut -d '"' -f 1-2)
    AST=$(echo "$LINE" | cut -d '"' -f 3- | grep -o "[^ ].*")
    FEATURES=$(echo "$AST" | BITS=30 MODE=sexpr TreeFeatures)
    echo "$PREFIX\" $FEATURES"
done
