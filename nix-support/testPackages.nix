{ lib, haskellPackages }:

with builtins;
with lib;
genAttrs [ "list-extras" ] (n: getAttr n haskellPackages)
