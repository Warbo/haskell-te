# Get the original nixpkgs path
{}:

(import ./tryElse.nix {}) <real> <nixpkgs>
