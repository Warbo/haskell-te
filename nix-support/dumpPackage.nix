{ dumpToNix, gnutar, lib, parseJSON, runScript }:
with builtins; with lib;

{ quick, src }: parseJSON (dumpToNix { inherit quick; pkgDir = "${src}"; }).outPath
