{ stdenv, jq, getDeps, utillinux, nix, cabal2db, doCheck ? true }:

with cabal2db;
cabal2db // rec {
  adb-scripts     = import ./scripts.nix         {
                      inherit stdenv jq getDeps utillinux nix doCheck; };
  annotateAsts    = import ./annotateAsts.nix    {
                      inherit stdenv adb-scripts;                      };
  runTypes        = import ./runTypes.nix        {
                      inherit withNix runScript adb-scripts jq;        };
  annotate        = import ./annotate.nix        {
                      inherit stdenv adb-scripts jq;                   };
  dumpAndAnnotate = import ./dumpAndAnnotate.nix {
                      inherit downloadAndDump;                         };
}
