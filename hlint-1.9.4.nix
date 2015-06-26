{ mkDerivation, base, cmdargs, containers, cpphs, directory
, filepath, haskell-src-exts, hscolour, process, stdenv
, transformers, uniplate
}:
mkDerivation {
  pname = "hlint";
  version = "1.9.4";
  sha256 = "0vqdkrhzxi99py9zrk01cz3hayfbp757rh1c1sgz00a1gf1pyz8m";
  isLibrary = true;
  isExecutable = true;
  buildDepends = [
    base cmdargs containers cpphs directory filepath haskell-src-exts
    hscolour process transformers uniplate
  ];
  homepage = "http://community.haskell.org/~ndm/hlint/";
  description = "Source code suggestions";
  license = stdenv.lib.licenses.bsd3;
}
