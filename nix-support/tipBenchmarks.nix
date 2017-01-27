{ bash, callPackage, defaultClusters, fetchFromGitHub, haskellPackages,
  nixFromCabal, pkgs, processPackage, runScript, stdenv, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else fetchFromGitHub {
                     owner  = "Warbo";
                     repo   = "theory-exploration-benchmarks";
                     rev    = "7b2682b";
                     sha256 = "0wg4b44lkp8xq0jwhkw2qsi1ynsfxskb1wldnzjnxxsg17waf8nn";
                   };
 in rec {
  inherit (callPackage path {
            inherit haskellPackages pkgs;
          })
    tip-benchmarks tools tip-benchmark-smtlib tip-benchmark-haskell;

  pkgDef = nixFromCabal (toString tip-benchmark-haskell) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, sampleSize ? null }:
              processPackage { inherit clusters sampleSize; }
                             pkg.name pkg;
}
