{ mkDerivation, base, containers, random, stdenv, template-haskell
, test-framework, tf-random, transformers
}:
mkDerivation {
  pname = "QuickCheck";
  version = "2.8";
  sha256 = "04xs6mq22bcnkpi616qrbm7jlivh9csnhmvjgp1ifq52an1wr4rx";
  buildDepends = [
    base containers random template-haskell tf-random transformers
  ];
  testDepends = [ base containers template-haskell test-framework ];
  homepage = "https://github.com/nick8325/quickcheck";
  description = "Automatic testing of Haskell programs";
  license = stdenv.lib.licenses.bsd3;
}
