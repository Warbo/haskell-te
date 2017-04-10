# Entry point for evaluating/building
with {
  pkgs = import ./nix-support {};
};
{
  inherit (pkgs) tests testSuite package;
}
