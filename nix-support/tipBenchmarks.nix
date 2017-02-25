{ bash, callPackage, defaultClusters, fetchFromGitHub, fetchgit,
  haskellPackages, nixFromCabal, pkgs, processPackage, runScript, stdenv,
  writeScript }:

with builtins;
let path = if any (x: x.prefix == "te-benchmarks") nixPath
              then <te-benchmarks>
              else let commit = {
                         rev    = "d405195";
                         sha256 = "0xxm7bak1jkl8h2impz6c2xlgzafkqpb21b56ardd5zijbgfs57h";
                       };
                    in if getEnv "OFFLINE" == ""
                          then fetchFromGitHub (commit // {
                            owner  = "Warbo";
                            repo   = "theory-exploration-benchmarks";
                          })
                          else fetchgit (commit // {
                            url = /home/chris/Programming/TheoryExplorationBenchmark;
                          });
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
