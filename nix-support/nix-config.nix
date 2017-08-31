{ mkNixpkgs, fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0s726wa2ygf2q5zhxf76sj8ww00sljv1kgf83rzhdapv9nbi3ri8";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0dyf0z9dhdczxvav01mx2bpxkjr052cz79zghm6mjlgv4kwf48ag";
  };

  rev    = "db71bf5";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = mkNixpkgs { config = import "${chosen}/config.nix"; };
}
