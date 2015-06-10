{ mkDerivation, base, containers, logict, mtl, stdenv }:
mkDerivation {
  pname = "unification-fd";
  version = "0.9.0";
  sha256 = "0fdnpcpcpjlxlwxpqlawwbgqhs1p9lrksy5ln5isyvr06hwqh7ki";
  buildDepends = [ base containers logict mtl ];
  homepage = "http://code.haskell.org/~wren/";
  description = "Simple generic unification algorithms";
  license = stdenv.lib.licenses.bsd3;
}
