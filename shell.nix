with import ./nix-support {};
runCommand "dummy" { buildInputs = [ package asv-nix ]; } "exit 1"
