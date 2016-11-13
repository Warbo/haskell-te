{ drvFromScript, dumpToNix, lib, stdParts, storeParts }:
with builtins; with lib;

{ quick, src }:
  drvFromScript
    {
      outputs = stdParts;
    }
    ''
      O=$(cat "${dumpToNix { inherit quick; pkgDir = "${src}"; }}")
      ${storeParts}
    ''
