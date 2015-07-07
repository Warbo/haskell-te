#! /usr/bin/env nix-shell
#! nix-shell -p treefeatures -p bash -p jq -i bash

set -e
set -x

while read -r LINE
do
    # Extract the "ast" value and pipe into TreeFeatures
    FEATURES=$(echo "$LINE" | jq -r '.ast' | BITS=30 MODE=sexpr TreeFeatures)

    # Read the features as a raw string, and collect into an array
    FEATARR=$(echo "$FEATURES" | jq -R '.' | jq -s '.')

    # Add the features to the object
    echo "$LINE" | jq -c ". + {features: \"$FEATURES\"}"
done
