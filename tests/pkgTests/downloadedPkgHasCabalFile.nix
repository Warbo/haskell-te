defs: with defs; pkg:

let source = downloadToNix pkg.name;
    files  = attrNames (builtins.readDir "${source}");
 in any (hasSuffix ".cabal") files
