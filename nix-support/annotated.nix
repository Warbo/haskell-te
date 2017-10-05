{ annotate, dumpToNix, nixedHsPkg }:

pkgDir: annotate rec {
  pkg    = { name = "dummy"; };
  asts   = dumpToNix { pkgDir = pkgSrc; };
  pkgSrc = nixedHsPkg pkgDir;
}
