with import <nixpkgs> {};

{treefeatures, hs2ast}:
stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;
  propagatedBuildInputs = [
    hs2ast
    treefeatures
    weka
    openjre
  ];
  installPhase = ''
    # Put scripts in $PATH
    mkdir -p "$out/bin"
    for SCRIPT in *.sh
    do
      NAME=$(basename "$SCRIPT" .sh)
      cp "$SCRIPT" "$out/bin/$NAME"
    done

    # Make it easy to run Weka
    cat <<'EOF' > "$out/bin/weka-cli"
      #!/bin/sh
      ${openjre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    EOF
    chmod +x "$out/bin/weka-cli"
  '';
  shellHook = ''
    # -jar weka.jar launches the GUI, -cp weka.jar runs from CLI
    function weka-cli {
      ${openjre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    }
  '';
}
