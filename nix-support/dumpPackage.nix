{ drvFromScript, dumpToNix, lib, stdParts, storeParts }:
with builtins; with lib;

{ src }:
  drvFromScript
    {
      outputs = stdParts;
    }
    ''
      O=$(cat "${dumpToNix { pkgDir = "${src}"; }}")
      ${storeParts}
    ''
