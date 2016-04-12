defs: with defs;
with lib;

assertMsg (hasSuffix "nix-support" <nixpkgs>)
          "<nixpkgs> is '${<nixpkgs>}'"
