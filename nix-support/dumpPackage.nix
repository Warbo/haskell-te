{ dumpToNix, gnutar, lib, runScript }:
with builtins; with lib;

{ quick, src }: dumpToNix { inherit quick; pkgDir = "${src}"; }
