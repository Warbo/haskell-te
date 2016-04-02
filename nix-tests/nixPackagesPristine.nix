defs: with defs;

# Make sure our augmented <nixpkgs> isn't polluted by custom definitions; these
# are some from my own ~/.nixpkgs/config.nix
let pkgs        = import <nixpkgs> {};
    hsPkgs      = haskellPackages;
    inAugmented = f: pkgs ? "${f}";
    doesntHave  = x: f: assertMsg (! x ? "${f}") "Don't have package '${f}'";
 in doesntHave pkgs   "warbo-utilities" &&
    doesntHave pkgs   "fs-uae"          &&
    doesntHave hsPkgs "haskell-example"
