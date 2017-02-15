# Entry point for evaluating/building
let pkgs = import ./nix-support {};
 in {

  tests = import ./nix-support/tests.nix {};

  package = import ./.;
}
