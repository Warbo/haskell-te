{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "1kxc6kjcjw4m89rn22dvphbq8cjjvdavdwq5avp7dj91269sqdkw";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0mlwrdd3g27fjby0dx615b12rakzbnk5fq8j9wdq1h8k4d3bav1i";
  };

  rev    = "2e25b18";

  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
import <nixpkgs> { config = import "${chosen}/config.nix"; }
