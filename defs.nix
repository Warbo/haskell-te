{ stdenv, jq, getDeps, utillinux, nix, cabal2db-defs, annotatedb }:

rec {
  inherit (cabal2db-defs) downloadAndDump;
  inherit annotatedb;
  annotateAsts    = import ./annotateAsts.nix    { inherit stdenv annotatedb;    };
  runTypes        = import ./runTypes.nix        { inherit stdenv annotatedb jq; };
  dumpAndAnnotate = import ./dumpAndAnnotate.nix { inherit downloadAndDump;      };
}
