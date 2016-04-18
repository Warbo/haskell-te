defs: with defs;

# Make sure our "prixtine" package set isn't polluted by custom definitions;
# these are some from my own ~/.nixpkgs/config.nix
let doesntHave  = x: f: assertMsg (! x ? "${f}") "Don't have package '${f}'";
 in doesntHave defs            "warbo-utilities" &&
    doesntHave defs            "fs-uae"          &&
    doesntHave haskellPackages "haskell-example"
