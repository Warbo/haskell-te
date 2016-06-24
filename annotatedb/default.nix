{ downloadAndDump, getDeps, jq, lib, nix, runScript, stdenv, utillinux }:

rec {
  annotateAsts    = import ./annotateAsts.nix    {
                      inherit stdenv adb-scripts;                      };

  dumpAndAnnotate = import ./dumpAndAnnotate.nix {
                      inherit downloadAndDump;                         };
}
