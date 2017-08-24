{ mkDerivation, base, cereal, QuickCheck, quickspec, stdenv
, testing-feat
}:
mkDerivation {
  pname = "tip-benchmark-sig";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base cereal QuickCheck quickspec testing-feat
  ];
  homepage = "http://example.org";
  description = "Auto-generated package for theory exploration";
  license = stdenv.lib.licenses.publicDomain;
}
