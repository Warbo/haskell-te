{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let allTests = mapAttrs (_: test: test pkgs) (pkgs.importDir ../tests);
 in pkgs.stripOverrides allTests
