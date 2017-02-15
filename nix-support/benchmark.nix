{ fetchFromGitHub, havePath, pkgs }:

with builtins;
with {
  src = if havePath "sample-bench"
           then import <sample-bench>
           else import (toString (fetchFromGitHub {
                  owner  = "Warbo";
                  repo   = "sample-bench";
                  rev    = "8d31ac4";
                  sha256 = "1byl395hm6xf57m0wy1352267cl3br5xl5bxdiz9v4gfwwhkny9s";
                }));
};
src { inherit pkgs; }
