with import <nixpkgs> {}; with builtins; with lib;

(callPackage ./default.nix {}).c2db-scripts
