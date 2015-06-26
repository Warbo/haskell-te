{ mkDerivation, array, base, containers, cpphs, directory
, filemanip, filepath, ghc-prim, happy, mtl, pretty, smallcheck
, stdenv, syb, tasty, tasty-golden, tasty-smallcheck
}:
mkDerivation {
  pname = "haskell-src-exts";
  version = "1.15.0.1";
  sha256 = "0xp5i06c478vn5m504ax5dfa7p5zc0kflbdkm2ijdzc779lpbx45";
  buildDepends = [ array base cpphs ghc-prim pretty ];
  testDepends = [
    base containers directory filemanip filepath mtl smallcheck syb
    tasty tasty-golden tasty-smallcheck
  ];
  buildTools = [ happy ];
  homepage = "https://github.com/haskell-suite/haskell-src-exts";
  description = "Manipulating Haskell source: abstract syntax, lexer, parser, and pretty-printer";
  license = stdenv.lib.licenses.bsd3;
}
