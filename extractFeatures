#!/bin/sh

# Perform feature extraction on ASTs from HS2AST

if [ "$#" -lt 2 ]
then
    echo "Please provide a source and a destination"
    exit 1
fi

function abs_dir {
    (cd "$1" &>/dev/null && printf "%s" "$PWD")
}

SOURCE=$(abs_dir "$1")
DEST=$(abs_dir "$2")

if [ ! -d "$SOURCE" ]
then
    echo "Source must be a directory"
    exit 1
fi

if [ ! -d "$DEST" ]
then
    echo "Destination must be a directory"
    exit 1
fi

echo "Extracting from $SOURCE to $DEST"

shopt -s nullglob
for PKG2 in "$SOURCE/"*
do
    PKG=$(basename "$PKG2")
    echo "Found package $PKG"
    mkdir -p "$DEST/$PKG"
    for MOD2 in "$SOURCE/$PKG/"*
    do
        MOD=$(basename "$MOD2")
        echo "Found module $MOD"
        mkdir -p "$DEST/$PKG/$MOD"
        for NAME2 in "$SOURCE/$PKG/$MOD/"*
        do
            NAME=$(basename "$NAME2")
            echo "Found name $NAME"
            MODE=sexpr BITS=30 TreeFeatures < "$SOURCE/$PKG/$MOD/$NAME" > "$DEST/$PKG/$MOD/$NAME"
        done
    done
done
