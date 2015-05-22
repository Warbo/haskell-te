#!/bin/sh

# Main ML4HS script

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a source of Haskell files"
    exit 1
fi

SOURCE=$1

if [ ! -d "$SOURCE" ]
then
    echo "Argument should be a directory (hopefully containing Haskell files)"
    exit 1
fi

# Set up temp directory to work in

function tmpdir {
    # First mktemp call works on Linux, second should handle OSX
    mktemp -d 2>/dev/null || mktemp -d -t 'ml4hs'
}

TEMP=$(tmpdir)

# List Haskell filenames

function files {
  # List all .hs and .lhs files in $SOURCE
  #OLD=$PWD
  #cd "$SOURCE"
  # Regular Haskell OR literate Haskell
  find "$SOURCE" \( -name "*.hs" -o -name "*.lhs" \) > "$TEMP/files"
  #cd "$OLD"
}

files

# Extract ASTs

mkdir -p "$TEMP/asts"
OLD=$PWD
cd "$TEMP/asts"
while read line
do
    echo "$line" | HS2AST
done < "$TEMP/files"
cd "$OLD"

# Extract features

mkdir -p "$TEMP/csvs"
OLD=$PWD
cd "$TEMP/csvs"
"$OLD/extractFeatures.sh" "$TEMP/asts" "$TEMP/csvs"
cd "$OLD"

#./cluster.sh "$TEMP"

#rm -rf "$TEMP"
