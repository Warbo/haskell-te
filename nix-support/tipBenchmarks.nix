{ bash, callPackage, defaultClusters, fetchFromGitHub, haskellPackages,
  nixFromCabal, pkgs, processPackage, runScript, stdenv, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else fetchFromGitHub {
                     owner  = "Warbo";
                     repo   = "theory-exploration-benchmarks";
                     rev    = "3b8e534";
                     sha256 = "1h5zpdy9f5pn11yaqjg8n626ms4c613ksa0kklhn29n566j4kp6b";
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
