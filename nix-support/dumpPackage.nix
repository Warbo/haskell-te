{ drvFromScript, dumpToNix, lib, stdParts, storeParts }:
with builtins; with lib;

{ quick, src }:
  drvFromScript
    {
      dumped  = dumpToNix { inherit quick; pkgDir = "${src}"; };
      outputs = stdParts;
    }
    ''
      O=$(cat "$dumped")
      ${storeParts}
    '';
