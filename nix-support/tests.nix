{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let tests  = pkgs.importDir ../tests;
 in mapAttrs (name: test: trace "Testing ${name}" test pkgs)
             tests
