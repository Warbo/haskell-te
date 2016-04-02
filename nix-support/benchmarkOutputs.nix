{ dumpToNix, gnutar, haskellPackages, lib, runScript, withNix }:
with lib;

let getTime        = name: result: result.time;
    getOutput      = name: result: result.stdout;
    dumpedPackages = import ./dumpedPackages.nix {
      inherit dumpToNix gnutar haskellPackages lib runScript withNix;
    };
in rec {
  quickDumpedPackages = dumpedPackages { quick = true;  };
  slowDumpedPackages  = dumpedPackages { quick = false; };
  dumpTimesQuick      = mapAttrs getTime   quickDumpedPackages;
  dumpTimesSlow       = mapAttrs getTime   slowDumpedPackages;
  quickDumps          = mapAttrs getOutput quickDumpedPackages;
  slowDumps           = mapAttrs getOutput slowDumpedPackages;
}
