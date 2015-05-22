#!/bin/sh

# Perform feature extraction on ASTs from HS2AST

if [ "$#" -lt 2 ]
then
    echo "Please provide a source and a destination"
    exit 1
fi

SOURCE=$1
DEST=$2

echo "Extracting from $SOURCE to $DEST"

shopt -s nullglob
for PKG in "$SOURCE/"*
do
    echo "Found package $PKG"
    mkdir -p "$DEST/$PKG"
    for MOD in "$SOURCE/$PKG/"*
    do
        echo "Found module $MOD"
        mkdir -p "$DEST/$PKG/$MOD"
        for NAME in "$SOURCE/$PKG/$MOD/"*
        do
            echo "Found name $NAME"
            MODE=sexpr BITS=30 TreeFeatures < "$SOURCE/$PKG/$MOD/$NAME" > "$DEST/$PKG/$MOD/$NAME"
        done
    done
done
