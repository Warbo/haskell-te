defs: with defs; pkg:
with builtins;

runCommand "canGetAsts-${pkg.pkg.name}"
  {
    inherit (pkg) asts;
    buildInputs = [ jq ];
  }
  ''
    jq 'length' < "$asts" | tee "$out" | jq -e '. > 0'
  ''
