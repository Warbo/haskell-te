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
OLD=$PWD
(cd "$TEMP/source"

 # Create a Nix expression from the .cabal file, if there isn't one already
 if [ ! -f "shell.nix" ]
 then
     cabal2nix --shell . > shell.nix
 fi

 # Wrap shell.nix with an expression including HS2AST's dependencies
 mv shell.nix shell2.nix
 cat << EOF > shell.nix
with import <nixpkgs> {};
import (shell2.nix).override (old: {
  buildDepends = old.buildDepends // hs2ast.buildDepends;
})
EOF

 nix-shell -I ~/Programming -p hs2ast --command "$OLD/extractAsts.sh \"$TEMP/asts\"")

# Extract features

mkdir -p "$TEMP/csvs"
(cd "$TEMP/csvs"
 nix-shell -I ~/Programming -p treefeats --command "$OLD/extractFeatures.sh \"$TEMP/asts\" \"$TEMP/csvs\""
)

./cluster.sh "$TEMP/csvs"

#rm -rf "$TEMP"
