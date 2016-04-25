{ downloadAndDump, getDeps, jq, lib, nix, runScript, stdenv, utillinux }:

rec {
  adb-scripts     = import ./scripts.nix         {
                      inherit stdenv jq getDeps utillinux; };
  annotateAsts    = import ./annotateAsts.nix    {
                      inherit stdenv adb-scripts;                      };

  dumpAndAnnotate = import ./dumpAndAnnotate.nix {
                      inherit downloadAndDump;                         };
}
