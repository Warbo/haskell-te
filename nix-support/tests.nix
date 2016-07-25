{ pkgs ? import ./. {} }:

with pkgs.lib;
with builtins;

let limit = ts: ts; #listToAttrs (map (n: nameValuePair n ts."${n}")
                    #             (take 2 (attrNames ts)));
    tests = pkgs.importDir ../tests;
 in mapAttrs (name: test: trace "Testing ${name}" test pkgs)
             (limit tests)
