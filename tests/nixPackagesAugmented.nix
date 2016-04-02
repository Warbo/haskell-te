defs: with defs;

assertMsg (hasSuffix "nix-support" <nixpkgs>)
          "<nixpkgs> is '${<nixpkgs>}'"
