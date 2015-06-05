with import <nixpkgs> {};

{treefeatures, hs2ast}
stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;
  buildInputs = [
    hs2ast
    treefeatures
    weka
    openjre
  ];

  shellHook = ''
    # -jar weka.jar launches the GUI, -cp weka.jar runs from CLI
    function weka-cli {
      ${openjre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    }
  '';
}
