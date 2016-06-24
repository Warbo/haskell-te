# Augments <nixpkgs> with our own packages and utilities
args:

let # When invoking Nix recursively, we want this set to be a pristine clone of
    # nixpkgs, however that would cause infinite recursion as we'd try to
    # augment ourselves. To prevent this, we also provide a "<real>" fallback
    # when calling Nix recursively.
    pkgs = with builtins;
           if any (p: p.prefix == "real") nixPath
              then import <real> {}
              else import ((import <nixpkgs> {}).fetchFromGitHub {
                            owner  = "NixOS";
                            repo   = "nixpkgs";
                            rev    = "16.03";
                            sha256 = "0m2b5ignccc5i5cyydhgcgbyl8bqip4dz32gw0c6761pd4kgw56v";
                          }) {};

    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'original.pristine'
    original = pkgs;

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
