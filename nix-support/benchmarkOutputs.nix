{ dumpToNix, gnutar, haskellPackages, lib, runScript, withNix }:
with lib;

let getTime = name: result: result.time;
in rec {
  quickDumpedPackages = import ./quickDumpedPackages.nix {
    inherit dumpToNix gnutar haskellPackages lib runScript withNix;
  };
  slowDumpedPackages  = {};
  dumpTimesQuick = mapAttrs getTime quickDumpedPackages;
  dumpTimesSlow  = mapAttrs getTime slowDumpedPackages;
}
