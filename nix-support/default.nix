# Augments <nixpkgs> with our own packages and utilities
args:

let pkgs = import <nixpkgs> {};
    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'original.pristine'
    original = if pkgs ? pristine then pkgs.pristine else real;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = import ./haskellPackages.nix {
                        inherit (original) haskellPackages;
                        nixFromCabal = import ./nixFromCabal.nix;
                      };

in original // original.callPackage ./defs.nix {
                 inherit haskellPackages;
               };
