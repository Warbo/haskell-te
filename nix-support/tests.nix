{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let

topLevel = mapAttrs (_: test: test pkgs) (pkgs.importDir ../tests);

pkgTests = import ./pkgTests.nix pkgs;

testDrvs = import ./testDrvs.nix pkgs;

allTests = { inherit pkgTests testDrvs topLevel; };

# Remove cruft, like "override" and "overrideDerivation"
strip = as: if isAttrs as
               then mapAttrs (n: strip)
                             (filterAttrs (n: v:
                                            !(elem n ["override"
                                                      "overrideDerivation"]))
                                          as)
               else as;

in strip allTests
