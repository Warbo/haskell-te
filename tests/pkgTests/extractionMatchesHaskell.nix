defs: with defs; pkg:

# extractFeatures is an old, slow version of our feature extraction algorithm.
# We use it here to check the output of our faster Haskell implementation.
let extractFeatures = writeScript "extract-features" ''
  #!/usr/bin/env bash

  # Arbitrary sizes for matrices
  export WIDTH=30
  export HEIGHT=30

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
'';

in drvFromScript { buildInputs = [ jq ML4HSFE ]; } ''
     set -e
     BASH_RESULT=$("${extractFeatures}" < "${pkg.annotated}" | jq '.') || {
       echo "Couldn't extract features with bash: $BASH_RESULT" 1>&2
       exit 2
     }

     RESULT=$(jq -n --argfile bash    <(echo "$BASH_RESULT")    \
                 --argfile haskell "${pkg.features}" \
                 '$bash == $haskell')

     if [[ "x$RESULT" = "xtrue" ]]
     then
       touch "$out"
     else
       echo "RESULT is '$RESULT'" 1>&2
       exit 1
     fi
   ''
