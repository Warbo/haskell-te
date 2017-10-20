# Uses OUT_DIR env var to include the package generated from smtlib data
(import <nixpkgs> {}).callPackage ./augmentedHs.nix {
  hsDir = builtins.getEnv "OUT_DIR";
}
