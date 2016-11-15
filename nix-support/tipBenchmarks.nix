{ bash, callPackage, defaultClusters, fetchurl, haskellPackages, nixFromCabal,
  processPackage, python, racket, runScript, stdenv, storeResult, writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else ../packages/te-benchmark;
 in rec {
  inherit (callPackage path {})
    tip-benchmarks tools tip-benchmark-smtlib;

  # Uses tip-benchmark-smtlib to produce a Haskell package
  tip-benchmarks-haskell = stdenv.mkDerivation {
    name         = "tip-benchmarks-haskell";
    buildInputs  = [ tools ];
                    SMT_FILE     = tip-benchmark-smtlib;
    buildCommand = ''
      source $stdenv/setup
      set -e

      export OUT_DIR="$out"
      mkdir -p "$OUT_DIR"

      # Create Haskell package
      full_haskell_package.rkt < "${tip-benchmark-smtlib}"
    '';
  };

  pkgDef = nixFromCabal (toString tip-benchmarks-haskell) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
