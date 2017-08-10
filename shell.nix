with import ./nix-support {};
runCommand "dummy" (withNix {
  buildInputs = [ package asv-nix git ];
}) "exit 1"
