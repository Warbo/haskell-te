{ makeHaskellPkgNixable, runCommand }:

dir: runCommand "nixified"
  { inherit dir; buildInputs = [ makeHaskellPkgNixable ]; }
  ''
    D=$(makeHaskellPkgNixable "$dir")
    ln -s "$D" "$out"
  ''
