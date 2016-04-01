# Custom definitions
{ bash, buildEnv, coreutils, gnutar, haskellPackages, jq, lib, nix, real,
  runCommand, stdenv, time, writeScript }:

rec {
  inherit (import ../cabal2db {
             inherit stdenv haskellPackages nix gnutar jq lib runCommand
                     writeScript;
          }) c2db-scripts runScript downloadToNix downloadAndDump importDir assertMsg withNix;

  inherit (import ./runBenchmark.nix {
             inherit bash coreutils explore-theories jq lib
                     mlspec-bench time writeScript;
           }) lastEntry withCriterion withTime
              benchmark;

  inherit (import ./benchmarkOutputs.nix {
             inherit dumpToNix gnutar haskellPackages lib runScript withNix;
          }) dumpTimesQuick dumpTimesSlow quickDumpedPackages slowDumpedPackages;

  dumpToNix = import ./dumpToNix.nix {
    inherit benchmark c2db-scripts parseJSON runScript withNix;
  };

  testPackageNames     = [ "list-extras" ];

  totalTimes           = import ./totalTimes.nix {
                           inherit haskellPackages lib;
                         };

  parseJSON            = import ./parseJSON.nix {
                           inherit jq runScript writeScript;
                         };

  annotatedb           = import ../packages/annotatedb       {
                           inherit getDeps;
                         };

  explore-theories     = import ../packages/explore-theories {
                           inherit stdenv;
                         };
  ml4hs                = import ../packages/ml4hs            {};

  annotateAsts         = import ./annotateAsts.nix           {
                           inherit annotatedb;
                         };
  dumpAndAnnotate      = import ./dumpAndAnnotate.nix        {
                           inherit dumpToNix annotateAsts;
                         };
  recurrent-clustering = import ../packages/recurrent-clustering {
                           inherit order-deps ML4HSFE annotatedb;
                         };

                         /*
  haskell-te = buildEnv {
    name = "haskell-te";
    paths = [
      # Our custom packages
      annotatedb explore-theories getDeps ML4HSFE mlspec-bench
      mlspec order-deps recurrent-clustering ml4hs

      # Standard utilities we need
      real.bash real.cabal-install real.cabal2nix real.coreutils
      real.findutils real.gnugrep real.gnused real.jq real.nix real.time
      real.utillinux
    ];
  };
*/

  # Include our overridden Haskell packages
  inherit haskellPackages;

  # Pull out Haskell packages (e.g. because they provide executables)
  inherit (haskellPackages) AstPlugin getDeps ML4HSFE mlspec mlspec-bench
                            order-deps;
}
