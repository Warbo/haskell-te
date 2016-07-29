{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let tests   = pkgs.importDir ../tests;

    # Our tests are implemented in Nix, so our "builder" is a call to nix-build.
    # We *could* import the test files directly, but that would cause all of the
    # tests to run at eval time, which can be frustrating (e.g. getting a list
    # of the tests would cause all of them to run!)
    runTest = name: value: pkgs.drvFromScript {} ''
      cd "${./..}"
      nix-build --no-out-link -E \
        'import ./tests/${name}.nix (import ./nix-support {})' || exit 1
      touch "$out"
    '';
 in mapAttrs runTest tests
