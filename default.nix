with import <nixpkgs> {};

{treefeatures, HS2AST, ArbitraryHaskell? {}, doCheck? false}:
stdenv.mkDerivation {
  name = "ml4hs";
  src  = ./.;
  propagatedBuildInputs = [
    HS2AST
    treefeatures
    weka
    jre
  ] ++ (if doCheck then [(haskellPackages.ghcWithPackages (p: [
                            p.tasty-quickcheck
                            ArbitraryHaskell
                        ]))]
                   else []);

  inherit doCheck;
  checkPhase = ''
    ./test.hs
  '';

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
      ${jre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    EOF
    chmod +x "$out/bin/weka-cli"
  '';
  shellHook = ''
    # -jar weka.jar launches the GUI, -cp weka.jar runs from CLI
    function weka-cli {
      ${jre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    }
  '';
}
