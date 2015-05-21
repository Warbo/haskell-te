#!/bin/sh

# Perform feature extraction on ASTs from HS2AST

if [ "$#" -lt 2 ]
then
    echo "Please provide a source and a destination"
    exit 1
fi

SOURCE=$1
DEST=$2

for PKG in $SOURCE
do
    mkdir -p "$DEST/$PKG"
    for MOD in "$SOURCE/$PKG"
    do
        mkdir -p "$DEST/$PKG/$MOD"
        for $NAME in "$SOURCE/$PKG/$MOD"
        do
            MODE=sexpr BITS=30 TreeFeatures < "$SOURCE/$PKG/$MOD/$NAME" > "$DEST/$PKG/$MOD/$NAME"
done
