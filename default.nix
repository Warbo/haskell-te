# The definitions from ./overlay.nix applied to a known-good nixpkgs version
with rec {
  helpersSrc = import ./nix-support/helpers.nix {
    inherit (import tePath {}) fetchFromGitHub;
  };

  tePath = import ./nix-support/path.nix {};

  helpers = import tePath {
    overlays = [ (import "${helpersSrc}/overlay.nix") ];
  };

  warn = args: if args == {}
                  then (x: x)
                  else builtins.trace
                         "Warning: Ignoring args to haskell-te default.nix";
};
args: warn args
  (import helpers.repo1803 { overlays = [ (import ./overlay.nix) ]; })
