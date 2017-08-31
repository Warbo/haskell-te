defs: with defs; pkg:

runCommand "haveDeps-${pkg.name}"
  {
    inherit (pkg) asts;
    buildInputs = [ jq ];
  }
  ''
    jq -e 'map(has("dependencies")) | all' < "$asts" > "$out"
  ''
