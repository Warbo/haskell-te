{ annotated, asv-nix, bash, cacheContent, callPackage, drvFromScript,
  fetchFromGitHub, fetchgit, haskellPackages, jq, nix-config, nix-config-src,
  nixFromCabal, nixpkgs-src, runCommand, stable, stdenv, tryElse, writeScript }:

with builtins;
with rec {
  path = tryElse <te-benchmarks> (nix-config.latestGit {
    url    = http://chriswarbo.net/git/theory-exploration-benchmarks.git;
    stable = {
      rev    = "ccf838d";
      sha256 = "1isbzv29903fh3m1sikj6gyaylq6wcw042wxna1g6k8wnlac9xjb";
    };
  });

  tebench  = callPackage path {
    inherit asv-nix haskellPackages nix-config-src;
    # Nixpkgs 17.03 disables Racket on i686, so always use 16.09 (for now)
    pkgsPath = nix-config.repo1609;
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
