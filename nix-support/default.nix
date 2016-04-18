# Augments <nixpkgs> with our own packages and utilities
args:

let # When invoking Nix recursively, we want this set to act as <nixpkgs>;
    # however, that would cause infinite recursion as we'd try to augment
    # ourselves. To prevent this, we also provide a "<real>" fallback when
    # calling Nix recursively.
    pkgs = with builtins; if any (p: p.prefix == "real") nixPath
                             then import <real>    {}
                             else import <nixpkgs> {};
    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'original.pristine'
    original = if pkgs ? pristine then pkgs.pristine else pkgs;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = import ./haskellPackages.nix {
                        inherit (original) haskellPackages;
                        nixFromCabal = import ./nixFromCabal.nix {
                                         inherit haskellPackages;
                                         inherit (original) lib stdenv;
                                       };
                      };

in original // original.callPackage ./defs.nix {
                 inherit haskellPackages;
               }
