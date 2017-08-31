defs: with defs; pkg:
with builtins;
with lib;

runCommand "clustersHaveFields-for-${pkg.name}"
  {
    inherit (pkg) clustered;
    buildInputs = [ fail jq ];
  }
  ''
    NUM=$(jq 'length' < "$clustered")
    [[ "$NUM" -gt 0 ]] || fail "No clusters"

    for field in arity name module type package ast features cluster \
                 quickspecable
    do
      jq -e "map(map(has(\"$field\")) | all) | all" < "$clustered"
    done

    echo pass > "$out"
  ''
