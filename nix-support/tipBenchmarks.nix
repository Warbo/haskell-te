{ annotated, asv-nix, bash, cacheContent, callPackage, defaultClusters,
  drvFromScript, fetchFromGitHub, fetchgit, haskellPackages, jq, nix-config-src,
  nixFromCabal, pkgs, runCommand, stdenv, writeScript }:

with builtins;
with rec {
  inherit (nix-config) sanitiseName;

  fallback = fetchFromGitHub {
               owner  = "Warbo";
               repo   = "theory-exploration-benchmarks";
               rev    = "35a8a28";
               sha256 = "1zzy30zsvcwvn7j47pla3arxwjbcimcp8rdsqkf6lzjvfxdb1s0b";
             };
  path     = with tryEval <te-benchmarks>;
             if success
                then value
                else fallback;
  tebench  = callPackage path {
    inherit asv-nix haskellPackages nix-config-src;
    pkgsPath = with tryEval <real>; if success then value else <nixpkgs>;
  };
};
rec {
  inherit path;
  inherit (tebench) tip-benchmarks cache env tools tip-benchmark-smtlib;
  annotatedAsts         = annotated tip-benchmark-haskell;
  pkg                   = haskellPackages.callPackage pkgDef {};
  pkgDef                = nixFromCabal (toString tip-benchmark-haskell) null;
  tip-benchmark-haskell = cacheContent "cached-benchmark-haskell"
                                       tebench.tip-benchmark-haskell;
}
