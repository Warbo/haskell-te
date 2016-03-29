{ dumpToNix, downloadToNix }:
pkgName: dumpToNix (builtins.unsafeDiscardStringContext "${downloadToNix pkgName}/source")
