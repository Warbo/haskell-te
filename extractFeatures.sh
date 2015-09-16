#! /usr/bin/env nix-shell
#! nix-shell -i bash -p ML4HSFE bash jq

source common.sh

# Arbitrary sizes for matrices
WIDTH=10
HEIGHT=10
export WIDTH
export HEIGHT

# Read in JSON array of all definitions
ALL=$(cat)

# Split up the array into lines and loop over them
echo "$ALL" | jq -c '.[]' | while read -r LINE
do
    # Extract the "ast" value for this entry
    AST=$(echo "$LINE" | jq -r '.ast')
    export AST

    # Call ML4HSFE, which will do feature-extraction on "AST". We send $ALL on
    # stdin so that ML4HSFE can look up previous cluster results.
    FEATURES=$(echo "$ALL" | ML4HSFE)

    # Add the features to the object
    echo "$LINE" | jq -c ". + {features: \"$FEATURES\"}"

# "Slurp" up the lines into another array
done | jq -s '.'
