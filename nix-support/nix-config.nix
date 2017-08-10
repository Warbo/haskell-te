{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0s7a7s8l8jm78wgxrcxv0hbvivs4ynk5ykdnb7kwwrlbm6xaky55";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "12576nyfdynyncfhgmhppmr6gcxhlc98w0vj97q1c6ay9mxxv0ad";
  };

  rev    = "eca9df2";

  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = import <nixpkgs> { config = import "${chosen}/config.nix"; };
}
