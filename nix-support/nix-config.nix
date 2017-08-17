{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0pxfpfl3l7s496swnif4ycx881dm6v0mkss270pyk0lvfgr6vmp8";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0w07spxxrgxdq0ghizgzjj578f30jpwldwzaq72cfiwl7khagcxz";
  };

  rev    = "354daf7";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = import <nixpkgs> { config = import "${chosen}/config.nix"; };
}
