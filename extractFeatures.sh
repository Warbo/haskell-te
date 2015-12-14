#! /usr/bin/env nix-shell
#! nix-shell -i bash -p ML4HSFE bash jq

# Arbitrary sizes for matrices
WIDTH=30
HEIGHT=30
export WIDTH
export HEIGHT

# Read in JSON array of all definitions
ALL=$(cat)

# Split up the array into lines and loop over them
echo "$ALL" | jq -c '.[]' | while read -r LINE
do
    # Extract the "ast" value for this entry
    AST=$(echo "$LINE" | jq -r '.ast')

    # We need to provide a list of all top-level names in this package/module
    # combo, since top-level names from the same module are treated as locals,
    # but we want them to be globals
    MOD=$(echo "$LINE" | jq -r '.module')
    PKG=$(echo "$LINE" | jq -r '.package')
    NAMES=$(echo "$ALL" | jq --arg mod "$MOD" --arg pkg "$PKG" -c \
                'map(select(.module == $mod and .package == $pkg)) | map(.name)')

    export MOD
    export PKG
    export NAMES

    # Call ML4HSFE, which will do feature-extraction on "AST"
    FEATURES=$(echo "$AST" | ML4HSFE)

    # Add the features to the object
    echo "$LINE" | jq -c --argfile features <(echo "$FEATURES") \
                      '. + {features: $features}'

# "Slurp" up the lines into another array
done | jq -s '.'
