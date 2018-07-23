# The definitions from ./overlay.nix applied to a known-good nixpkgs version
with rec {
  helpersSrc = import ./nix-support/helpers.nix {
    inherit (import <nixpkgs> {}) fetchFromGitHub;
  };

  helpers = import <nixpkgs> {
    overlays = [ (import "${helpersSrc}/overlay.nix") ];
  };

  warn = args: if args == {}
                  then builtins.trace
                         "Warning: Ignoring args to haskell-te default.nix"
                  else (x: x);
};
args: warn args
  (import helpers.repo1803 { overlays = [ (import ./overlay.nix) ]; })
