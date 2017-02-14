{ fetchFromGitHub, havePath, pkgs }:

with builtins;
with {
  src = if havePath "sample-bench"
           then import <sample-bench>
           else import (toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "50c2342";
                  sha256 = "0rzjvm20pvar3rwn31h3g7jv3yl5a1xd24dz9wik231n3q48mm2y";
                }));
};
src { inherit pkgs; }
