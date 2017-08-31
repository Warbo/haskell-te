defs: with defs; pkg:
with builtins;
with lib;

runCommand "canCluster"
  { inherit (pkg) clustered; }
  ''
    echo pass > "$out"
  ''
