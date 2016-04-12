defs: with defs; pkg:
with builtins;
with lib;

let source = downloadToNix pkg.name;
    files  = attrNames (builtins.readDir "${source}");
 in any (hasSuffix ".cabal") files
