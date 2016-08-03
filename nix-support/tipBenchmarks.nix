{ bash, defaultClusters, fetchurl, haskellPackages, nixFromCabal,
  processPackage, python, racket, runScript, stdenv, storeResult, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else ../packages/te-benchmark;
 in rec {
  inherit (import path {
             inherit bash fetchurl haskellPackages python racket stdenv
                     writeScript;
           })
    tip-benchmarks;

  module = tip-benchmarks;

  pkgDef = nixFromCabal (toString module) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
