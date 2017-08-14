{ annotated, asv-nix, bash, cacheContent, callPackage, defaultClusters,
  drvFromScript, fetchFromGitHub, fetchgit, haskellPackages, jq, nix-config-src,
  nixFromCabal, pkgs, runCommand, runScript, stdenv, writeScript }:

with builtins;
with rec {
  inherit (nix-config) sanitiseName;

  fallback = fetchFromGitHub {
               owner  = "Warbo";
               repo   = "theory-exploration-benchmarks";
               rev    = "79d33e2";
               sha256 = "1icpxjldlgwxacb0brjpn72yrq2asbg74kmymdkk9y8qvxny9ib0";
             };
  path     = if any (x: x.prefix == "te-benchmarks") nixPath
                then <te-benchmarks>
                else fallback;
  tebench  = callPackage path {
    inherit asv-nix haskellPackages nix-config-src;
    pkgsPath = with tryEval <real>; if success then value else <nixpkgs>;
  };
};
rec {
  inherit (tebench) tip-benchmarks cache env tools tip-benchmark-smtlib;
  annotatedAsts = annotated (toString tip-benchmark-haskell);
  pkg           = haskellPackages.callPackage pkgDef {};
  pkgDef        = nixFromCabal (toString tip-benchmark-haskell) null;
  tip-benchmark-haskell = cacheContent "cached-benchmark-haskell"
                                       tebench.tip-benchmark-haskell;
}
