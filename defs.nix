{ stdenv, jq, getDeps, utillinux, nix, cabal2db-defs, annotatedb }:

rec {
  inherit (cabal2db-defs) downloadAndDump;
  inherit annotatedb;
  annotateAsts    = import ./annotateAsts.nix    { inherit stdenv annotatedb; };
  dumpAndAnnotate = import ./dumpAndAnnotate.nix { inherit downloadAndDump;   };
}
