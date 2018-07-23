# Provides an augmented package set to use instead of <nixpkgs>
with builtins;
with rec {
  # If we have a <real> path, use that as the source of fetchFromGitHub, to
  # prevent an infinite loop. Otherwise use <nixpkgs> as normal.
  path = import ./path.nix {};

  # nix-config defines a bunch of stable package sets we can use
  inherit ((import path {}).callPackage ./nix-config.nix { inherit path; })
    nix-config;

  pkgs = nix-config { unstablePath = path; };
};
assert pkgs ? nixpkgs1603 || abort "No nixpkgs1603 found";
assert pkgs ? nixpkgs1609 || abort "No nixpkgs1609 found";
rec {
  inherit pkgs;
  nixpkgs-2016-03  = pkgs.nixpkgs1603;
  nixpkgs-2016-09  = pkgs.nixpkgs1609;
  nixpkgs          = nixpkgs-2016-03;
  nix-config       = pkgs.customised.nixpkgs1603;
}
