{ dumpToNix, gnutar, lib, parseJSON, runScript }:
with builtins; with lib;

{ quick, src }:
  parseJSON
    (readFile
      (toString (dumpToNix { inherit quick; pkgDir = "${src}"; })))
