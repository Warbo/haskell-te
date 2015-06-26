#!/bin/sh

# Main ML4HS script

shopt -s nullglob

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide the location of a Haskell project"
    exit 1
fi

SOURCE=$1

if [ ! -d "$SOURCE" ]
then
    echo "Argument should be a directory containing a Haskell project"
    exit 1
fi

INVALID=1
for CABAL in "$SOURCE"/*.cabal
do
    echo "Found cabal"
    INVALID=0
done

if [ $INVALID -eq 1 ]
then
    echo "No .cabal file found in the given directory"
    exit 1
fi

# Set up temp directory to work in

# First mktemp call works on Linux, second should handle OSX
TEMP=$(mktemp -d 2>/dev/null || mktemp -d -t 'ml4hs')

# Duplicate the source (to avoid side-effects)

cp -rL "$SOURCE" "$TEMP/source"

# Extract Haskell ASTs

mkdir "$TEMP/asts"

(cd "$TEMP/source"
 extractAsts "$TEMP/asts")

# Extract features

mkdir -p "$TEMP/csvs"
(cd "$TEMP/csvs"
 extractFeatures "$TEMP/asts" "$TEMP/csvs")

cluster "$TEMP/csvs"

rm -rf "$TEMP"
