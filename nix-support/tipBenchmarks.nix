{ bash, defaultClusters, haskellPackages, nixFromCabal,
  processPackage, racket, runScript, stdenv, storeResult, writeScript }:

rec {
  inherit (import ../packages/te-benchmark {
             inherit bash haskellPackages racket stdenv writeScript;
           })
    te-benchmark tip-benchmarks;

  path  = ../packages/te-benchmark;

  module = tip-benchmarks;

  pkgDef = nixFromCabal (toString module) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
