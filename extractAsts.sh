#!/bin/sh

# Extract ASTs from Haskell projects

if [ "$#" -lt 1 ]
then
    echo "Please provide a destination"
    exit 1
fi

function abs_dir {
    (cd "$1" &>/dev/null && printf "%s" "$PWD")
}

DEST=$(abs_dir $1)

echo "Writing to $1 ($DEST)"

if [ ! -d "$DEST" ]
then
    echo "Dest must be a directory ($DEST)"
    exit 1
fi

find . -iname "*.hs" -o -iname "*.lhs" | while read LINE
                                         do
                                             echo "Scanning $LINE into $DEST"
                                             echo "$LINE" | HS2AST "$DEST"
                                         done
