{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "15bwcn8n15i97a5c3csc9v1af8n72v17m5vnayk57kmdkia6zwx8";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0yrqhi9lbckybzjhanmfai6mm6ijdpcg8qj1vkyxpv7cwl7h1yzm";
  };

  rev    = "c6e153c";

  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
import <nixpkgs> { config = import "${chosen}/config.nix"; }
