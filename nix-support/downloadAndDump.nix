{ dumpToNix, downloadToNix }:
{ quick, pkgName}:

dumpToNix { inherit quick; pkgDir = downloadToNix pkgName; }
