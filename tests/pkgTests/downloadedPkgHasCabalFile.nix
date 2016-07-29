defs: with defs; pkg:
with builtins;
with lib;

let source = downloadToNix pkg.name;
    files  = attrNames (builtins.readDir "${source}");
 in testMsg (any (hasSuffix ".cabal") files)
            "Downloading ${pkg.name} gets cabal file"
