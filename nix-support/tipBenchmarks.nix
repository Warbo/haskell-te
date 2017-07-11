{ annotated, bash, callPackage, defaultClusters, fetchFromGitHub, fetchgit,
  haskellPackages, nixFromCabal, pkgs, processPackage, runScript, stdenv,
  writeScript }:

with builtins;
rec {
  path = if any (x: x.prefix == "te-benchmarks") nixPath
            then <te-benchmarks>
            else fetchFromGitHub {
                   owner  = "Warbo";
                   repo   = "theory-exploration-benchmarks";
                   rev    = "2285111";
                   sha256 = "0s4arrrvihzbh471zvrwj9x6j6fv500pv9q8vpbgvgj7zdd6np09";
                 };

  inherit (callPackage path {
            inherit haskellPackages pkgs;
          })
    tip-benchmarks cache env tools tip-benchmark-smtlib tip-benchmark-haskell;

  pkgDef = nixFromCabal (toString tip-benchmark-haskell) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, sampleSize ? null }:
              processPackage { inherit clusters sampleSize; }
                             pkg.name pkg;

  annotatedAsts = annotated (toString tip-benchmark-haskell);
}
