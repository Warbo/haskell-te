defs: with defs; pkg:
with builtins;
with lib;

runCommand "haveEquations-${pkg.name}"
  {
    inherit (pkg) eqs;
    buildInputs = [ jq ];
  }
  ''
    jq -e 'type == "array"'            < "$eqs" >> "$out"
    jq -e 'map(has("relation")) | all' < "$eqs" >> "$out"
  ''
