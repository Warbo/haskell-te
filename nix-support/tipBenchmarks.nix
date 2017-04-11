{ bash, callPackage, defaultClusters, fetchFromGitHub, fetchgit,
  haskellPackages, nixFromCabal, pkgs, processPackage, runScript, stdenv,
  writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else fetchFromGitHub {
                     owner  = "Warbo";
                     repo   = "theory-exploration-benchmarks";
                     rev    = "b1051b4";
                     sha256 = "07frjppdaq16jfybnbhs244yszb660yfmxf4mwmasx4a6gyxyy61";
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
