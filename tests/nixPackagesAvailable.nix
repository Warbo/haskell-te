defs: with defs;
with builtins;

let doTest = n: testMsg (isAttrs defs."${name}") "${name} is a set";
 in testWrap "All packages available" (map doTest [
      "mlspec"
      "mlspec-bench"
      "haskellPackages.ArbitraryHaskell"
      "haskellPackages.mlspec"
      "haskellPackages.mlspec-bench"
      "haskellPackages.mlspec-helper"
      "haskellPackages.nix-eval"
      "haskellPackages.runtime-arbitrary"
    ])
