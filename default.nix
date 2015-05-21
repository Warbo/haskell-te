with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;
  buildInputs = [
    hs2ast
    treefeats
    weka
  ];
}
