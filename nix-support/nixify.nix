{ makeHaskellPkgNixable, runCommand }:

dir: runCommand "nixified"
  {
    inherit dir;
    buildInputs = [ makeHaskellPkgNixable ];
    SKIP_NIX    = "1";
  }
  ''
    set -e
    D=$(makeHaskellPkgNixable "$dir")
    cp -r "$D" "$out"
  ''
