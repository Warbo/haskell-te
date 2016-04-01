# Takes a directory D, returns { F = import D/F.nix; ... } for all F.nix in D
{ lib }:
with lib;

dir:

let addFile = x: old: old // builtins.listToAttrs [{
                               name  = lib.removeSuffix ".nix" x;
                               value = import (dir + "/${x}");
                             }];
 in fold addFile {}
         (filter (hasSuffix ".nix")
                 (builtins.attrNames (builtins.readDir dir)))
