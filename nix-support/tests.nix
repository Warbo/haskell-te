{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let

allTests = mapAttrs (_: test: test pkgs) (pkgs.importDir ../tests);

# Remove cruft, like "override" and "overrideDerivation"
strip = as: if isAttrs as
               then mapAttrs (n: strip)
                             (filterAttrs (n: v:
                                            !(elem n ["override"
                                                      "overrideDerivation"]))
                                          as)
               else as;

in strip allTests
