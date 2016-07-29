{ dumpToNix, downloadToNix, parseJSON }:
{ quick, pkgName}:

with builtins;

let dump = dumpToNix { inherit quick; pkgDir = downloadToNix pkgName; };
 in parseJSON (readFile "${dump}")
