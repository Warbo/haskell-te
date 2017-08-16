{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0wqp4pa4jpgf525l2b48ax4zy1mf1rmjnq1bw4ckprcw87bpfgdd";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0773m3mmznddfmfacvgh1x5h22wkdzfy62n82a1pd0pnsilhhc4a";
  };

  rev    = "10c8efb";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;
};
{
  nix-config-src = chosen;
  nix-config     = import <nixpkgs> { config = import "${chosen}/config.nix"; };
}
