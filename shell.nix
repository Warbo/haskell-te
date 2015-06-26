# This is equivalent to giving default.nix some default parameters. However,
# these packages aren't (yet?) in Nixpkgs, so it won't work unless we define
# them ourselves somewhere, eg. in ~/.nixpkgs/config.nix. That's why we use this
# separate shell.nix file, so that default.nix is usable as-is.

# If you just want to get up and running, take a look at
# http://chriswarbo.net/git/haskell-te , which defines these expressions.

with import <nixpkgs> {};
callPackage ./. {
  inherit treefeatures HS2AST ArbitraryHaskell;
  doCheck = true;
}
