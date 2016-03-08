# Make sure you use 'NIX_PATH="$(./nix-support/nixPath.sh)" or equivalent!
assert builtins.typeOf <real> == "path";
(import <nixpkgs> {}).haskell-te
