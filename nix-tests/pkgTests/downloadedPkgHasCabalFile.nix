defs: with defs; pkgName:

let source = downloadToNix pkgName;
    files  = attrNames (builtins.readDir "${source}");
 in any (hasSuffix ".cabal") files
