{ pkgs ? import ./. {} }:

let tests = pkgs.importDir ../tests;
 in pkgs.lib.mapAttrs (name: test: test pkgs) tests
