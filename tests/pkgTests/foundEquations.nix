defs: with defs; pkg:
with builtins;
with lib;

runCommand "${pkg.name}-eqs-found"
  {
    inherit (pkg) eqs;
    buildInputs = [ fail jq ];
  }
  ''
    jq -e 'length | . > 0' < "$eqs"
    echo pass > "$out"
  ''
