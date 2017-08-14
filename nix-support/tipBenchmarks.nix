{ annotated, bash, callPackage, defaultClusters, fetchFromGitHub, fetchgit,
  haskellPackages, nix-config-src, nixFromCabal, pkgs, runScript, stdenv,
  writeScript }:

with builtins;
rec {
  fallback = fetchFromGitHub {
               owner  = "Warbo";
               repo   = "theory-exploration-benchmarks";
               rev    = "79d33e2";
               sha256 = "1icpxjldlgwxacb0brjpn72yrq2asbg74kmymdkk9y8qvxny9ib0";
             };
  path     = if any (x: x.prefix == "te-benchmarks") nixPath
                then <te-benchmarks>
                else fallback;

  inherit (callPackage path {
            inherit haskellPackages pkgs;
          })
    tip-benchmarks cache env tools tip-benchmark-smtlib tip-benchmark-haskell;

  pkgDef = nixFromCabal (toString tip-benchmark-haskell) null;

  pkg = haskellPackages.callPackage pkgDef {};

  annotatedAsts = annotated (toString tip-benchmark-haskell);
}
