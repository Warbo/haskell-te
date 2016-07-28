{ dumpToNix, downloadToNix }:
{ quick, pkgName}:

parseJSON (dumpToNix { inherit quick; pkgDir = downloadToNix pkgName; })
