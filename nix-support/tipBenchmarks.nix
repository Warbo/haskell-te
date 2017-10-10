{ asv-nix, callPackage, haskellPackages, nix-config, nix-config-src, tryElse }:

with builtins;
with {
  path = tryElse <te-benchmarks> (nix-config.latestGit {
    url    = http://chriswarbo.net/git/theory-exploration-benchmarks.git;
    stable = {
      rev    = "ccf838d";
      sha256 = "1isbzv29903fh3m1sikj6gyaylq6wcw042wxna1g6k8wnlac9xjb";
    };
  });
};
{ inherit path; } // callPackage path {
  inherit asv-nix haskellPackages nix-config-src;

  # Nixpkgs 17.03 disables Racket on i686, so always use 16.09 (for now)
  pkgsPath = nix-config.repo1609;
}
