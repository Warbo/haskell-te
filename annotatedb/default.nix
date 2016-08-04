{ downloadAndDump, GetDeps, jq, lib, nix, runScript, stdenv, utillinux }:

rec {
  annotateAsts    = import ./annotateAsts.nix    {
                      inherit stdenv;
                    };

  dumpAndAnnotate = import ./dumpAndAnnotate.nix {
                      inherit downloadAndDump;
                    };
}
