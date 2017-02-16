{ fetchFromGitHub, havePath, pkgs }:

with builtins;
rec {
  src = if havePath "sample-bench"
           then <sample-bench>
           else toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "f16bbba";
                  sha256 = "0szjv1whg9cxkqkpj7h96y909kzpd35ipr0hj0fdwcgxfvdfyfvm";
                });

  benchmark = import src { inherit pkgs; };

  timeout = pkgs.callPackage "${src}/timeout.nix" {};
}
