{ bash, callPackage, defaultClusters, fetchFromGitHub, haskellPackages,
  nixFromCabal, pkgs, processPackage, runScript, stdenv, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else fetchFromGitHub {
                     owner  = "Warbo";
                     repo   = "theory-exploration-benchmarks";
                     rev    = "da44ffde9dfbb9931c9713783212c4b4cf7e648d";
                     sha256 = "1z8382nywm56k9ciy605bnljdmq6pyfwwr2whkdmf9x2ld2bdwnz";
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
