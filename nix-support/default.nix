# A clean clone of nixpkgs, augmented with our own packages and utilities
args:

let

# Some of our scripts invoke Nix, using the usual '<nixpkgs>' path to access
# definitions. We override that path (see 'withNix') to point at this file, so
# that the same versions are used everywhere.

pkgs = import ./nixpkgs.nix args;

# haskellPackages.override ensures dependencies are overridden too
haskellPackages = import ./haskellPackages.nix {
                    inherit (pkgs) haskellPackages;
                    nixFromCabal = import ./nixFromCabal.nix {
                                     inherit haskellPackages;
                                     inherit (pkgs) lib stdenv;
                                   };
                  };

in pkgs // pkgs.callPackage ./defs.nix {
             inherit haskellPackages;
           }
