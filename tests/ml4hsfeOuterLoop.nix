defs: with defs;
with builtins;

drvFromScript { EXAMPLE = let f = ./ml4hsfeExamples/ml4hsfe-outer-loop-example-input.json;
                           in drvFromScript {} ''
                                # Select 50 random ASTs
                                ASTS=$(jq -c '.[]' < "${f}")
                                echo "$ASTS" | shuf | head -n50 | \
                                  jq -s '.' > "$out"
                              '';
                buildInputs = [ haskellPackages.ML4HSFE runWeka ]; } ''
  set -e

  export WIDTH=30
  export HEIGHT=30
  export CLUSTERS=4

  ml4hsfe-outer-loop < "$EXAMPLE" | jq '.'

  touch "$out"
''
