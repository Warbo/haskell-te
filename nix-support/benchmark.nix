{ fetchFromGitHub, havePath, pkgs }:

with builtins;
with {
  src = if havePath "sample-bench"
           then import <sample-bench>
           else import (toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "60468ed";
                  sha256 = "1ll22w9lzn91h8lvfjplm00ddfc31c2drwa31645yia1krfabvxc";
                }));
};
src { inherit pkgs; }
