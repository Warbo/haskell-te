{ fetchFromGitHub, havePath, nix, nix-config, pkgs, pythonPackages, runCommand,
  time, withNix, writeScript }:

with builtins;
rec {
  src = if havePath "sample-bench"
           then <sample-bench>
           else toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "d71e333";
                  sha256 = "1hgdnh4lqgl1gdniggriqql9l2vhr63fg33vs9dqfs2m3zhaj18a";
                });

  benchmark = import src { inherit pkgs; };

  timeout = pkgs.callPackage "${src}/timeout.nix" {};
}
