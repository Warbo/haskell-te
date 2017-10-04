{ pkgs ? import ../nix-support {} }:

with builtins;
with pkgs.lib;
with {
  allTests = mapAttrs (_: test: test pkgs)
                      # Don't include this default.nix file
                      (removeAttrs (pkgs.importDir ./.) [ "default" ]);
};

pkgs.stripOverrides allTests
