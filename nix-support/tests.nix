{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let

# Turn each test file into a derivation. We *could* import them directly,
# but that would cause all of the tests to run at eval time, which is
# frustrating (e.g. getting a list of the tests would cause all of them to
# run!)
runTest = name: value: pkgs.runTestInDrv "tests/${name}.nix" [];

tests   = mapAttrs runTest (pkgs.importDir ../tests);

in tests // { pkgTests = import ./pkgTests.nix pkgs; }
