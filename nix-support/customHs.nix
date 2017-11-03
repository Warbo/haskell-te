# Uses OUT_DIRS env var to include the packages generated from TIP data
with builtins;
(import <nixpkgs> {}).callPackage ./augmentedHs.nix {
  hsDirs = fromJSON (getEnv "OUT_DIRS");
}
