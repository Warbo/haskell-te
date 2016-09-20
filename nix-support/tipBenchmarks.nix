{ bash, callPackage, defaultClusters, fetchurl, haskellPackages, nixFromCabal,
  processPackage, python, racket, runScript, stdenv, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else ../packages/te-benchmark;
 in rec {
  inherit (callPackage path {})
    te-benchmark tip-benchmarks te-benchmark-tests tip-benchmark-smtlib;

  pkgDef = nixFromCabal (toString tip-benchmarks) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
