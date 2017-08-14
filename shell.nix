with import ./nix-support {};
runCommand "haskell-te-env" (withNix {
  buildInputs = [ package asv-nix git ];
}) "exit 1"
