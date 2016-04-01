with import <nixpkgs> {}; with builtins; with lib;

callPackage ./default.nix { doCheck = false; }
