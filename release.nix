# Entry point for evaluating/building
let pkgs = import ./nix-support {};
 in {

  tests = import ./nix-support/tests.nix {};

  package = import ./.;

  stabilisePlot = import ./nix-support/stabilisePlot.nix;
}
