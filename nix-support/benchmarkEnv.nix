{ asv-nix, git, package, runCommand, withNix }:

runCommand "haskell-te-env" (withNix {
  buildInputs = [ package asv-nix git ];
}) "exit 1"
