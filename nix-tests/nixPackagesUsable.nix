defs: with defs;

let usable = x: pathExists (unsafeDiscardStringContext "${x}");
in all usable [
  explore-theories
  mlspec
  mlspec-bench
  haskellPackages.ArbitraryHaskell
  haskellPackages.mlspec
  haskellPackages.mlspec-bench
  haskellPackages.mlspec-helper
  haskellPackages.nix-eval
  haskellPackages.runtime-arbitrary
]
