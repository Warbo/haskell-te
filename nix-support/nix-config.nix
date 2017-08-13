{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0wn0vjzz975fkrgl7g3h26pjcm5ja2ylzb5d09kf1apkivdxmvfi";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0isnxvv11lddhdh43pz08rh0an84jfpcdgc9rlbb8hk4dqknkhr1";
  };

  rev    = "bf94098";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = import <nixpkgs> { config = import "${chosen}/config.nix"; };
}
