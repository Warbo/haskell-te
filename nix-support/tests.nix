{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let

# Turn each test file into a derivation. We *could* import them directly,
# but that would cause all of the tests to run at eval time, which is
# frustrating (e.g. getting a list of the tests would cause all of them to
# run!)
runTest  = name: value: pkgs.runTestInDrv "tests/${name}.nix" [];

topLevel = mapAttrs runTest (pkgs.importDir ../tests);

pkgTests = import ./pkgTests.nix pkgs;

allTests = { inherit pkgTests topLevel; };

# Remove cruft, like "override" and "overrideDerivation"
strip = as: if isAttrs as
               then mapAttrs (n: strip)
                             (filterAttrs (n: v:
                                            !(elem n ["override"
                                                      "overrideDerivation"]))
                                          as)
               else as;

in strip allTests
