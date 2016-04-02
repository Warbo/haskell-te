{ downloadAndDump, getDeps, jq, lib, nix, runScript, stdenv, utillinux, withNix }:

rec {
  adb-scripts     = import ./scripts.nix         {
                      inherit stdenv jq getDeps utillinux; };
  annotateAsts    = import ./annotateAsts.nix    {
                      inherit stdenv adb-scripts;                      };
  runTypes        = import ./runTypes.nix        {
                      inherit withNix runScript adb-scripts jq;        };
  annotate        = import ./annotate.nix        {
                      inherit runScript adb-scripts jq withNix;        };

  dumpAndAnnotate = import ./dumpAndAnnotate.nix {
                      inherit downloadAndDump;                         };
}
