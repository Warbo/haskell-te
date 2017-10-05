allArgs:

# Provides an augmented package set to use instead of <nixpkgs>
with builtins;
with rec {
  args = removeAttrs allArgs [ "stable" ];

  # Default to a known, stable set of packages. Pass in 'false' to check against
  # the latest versions of everything.
  stable = args.stable or true;

  # If we have a <real> path, use that as the source of fetchFromGitHub, to
  # prevent an infinite loop. Otherwise use <nixpkgs> as normal.
  path = import ./path.nix {};

  # nix-config defines a bunch of stable package sets we can use
  configs = (import path { config = {}; }).callPackage ./nix-config.nix {
    inherit path stable;
  };
  config  = configs.nix-config;

  pkgs    = import path { inherit config; };

  default = if stable then pkgs.repo1603 else path;

  tryElse = import ./tryElse.nix {};
};
rec {
  inherit (configs) nix-config-src;
  nixpkgs-src      = default;
  nixpkgs-2016-03  = import pkgs.repo1603 args;
  nixpkgs-2016-09  = import pkgs.repo1609 args;
  nixpkgs          = import default args;
  nix-config       = import default (args // { inherit config; });
}
