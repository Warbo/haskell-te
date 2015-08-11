with import <nixpkgs> {};

runCommand
  "weka-cli"
  { propagatedBuildInputs = [ jre weka ]; }
  ''
    # Make it easy to run Weka
    mkdir -p "$out/bin"
    cat <<'EOF' > "$out/bin/weka-cli"
    #!bin/sh
    ${jre}/bin/java -Xmx1000M -cp ${weka}/share/weka/weka.jar "$@"
    EOF
    chmod +x "$out/bin/weka-cli"
  ''
