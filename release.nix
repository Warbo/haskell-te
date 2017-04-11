# Entry point for evaluating/building
with {
  pkgs = import ./nix-support {};
};
pkgs.stripOverrides {
  inherit (pkgs) tests testSuite package;
}
