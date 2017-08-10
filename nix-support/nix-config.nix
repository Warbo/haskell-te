{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "1kkjdn0bhc9wii3hmi27v0snzkckr44pcg7k2n1p32bg3mmgfi6x";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "1zx5bmqxzibz0jcx46ghscl7vx3imvpwjp3lwv9bkcfkxfqc03q6";
  };

  rev    = "cd88c9a";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = import <nixpkgs> { config = import "${chosen}/config.nix"; };
}
