defs: with defs; with builtins; pkg:

runCommand "reduceProducesEqs-${pkg.name}"
  {
    inherit (pkg) eqs;
    buildInputs = [ jq reduce-equations ];
  }
  ''
    GOT=$(reduce-equations < "$eqs")
    echo "$GOT" | jq -e 'type == "array"'
    echo "$GOT" | jq -e 'map(has("relation")) | all' > "$out"
  ''
