{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0m0rxvcf18adbmdmr3hdrdzrkj90rs1fa3sm6gl8rbvlzmimmnh7";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0qx09sn4c6npcf9j8hh87fz9lq0fhyq611l8dp3x58bqxvnrs4l0";
  };

  rev    = "6750e46";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;

  path = with tryEval <real>;
         if success then value else <nixpkgs>;
};
{
  nix-config-src = chosen;
  nix-config     = import path { config = import "${chosen}/config.nix"; };
}
