with import <nixpkgs> {};

{ArbitraryHaskell}:
stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;
  propagatedBuildInputs = [
    (haskellPackages.ghcWithPackages (p: [
      p.QuickCheck
      p.tasty
      p.tasty-quickcheck
      ArbitraryHaskell
    ]))
  ];
}
