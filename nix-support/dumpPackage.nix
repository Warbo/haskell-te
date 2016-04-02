{ dumpToNix, gnutar, lib, runScript, withNix }:
with builtins; with lib;

{ quick, src }: dumpToNix { inherit quick; pkgDir = "${src}"; }
