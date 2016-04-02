# Custom definitions
{ bash, bc, buildEnv, coreutils, gnutar, haskellPackages, jq, lib, nix, pv,
  real, runCommand, stdenv, time, utillinux, wget, writeScript }:

rec {
  inherit coreutils;

  inherit (import ../cabal2db {
             inherit stdenv haskellPackages nix gnutar jq lib runCommand
                     writeScript;
          }) runScript importDir withNix;

  inherit (import ../annotatedb {
             inherit getDeps jq lib nix runScript stdenv utillinux withNix;
          }) adb-scripts annotateAsts runTypes annotate dumpAndAnnotate;

  inherit (import ./runBenchmark.nix {
             inherit bash coreutils explore-theories jq lib
                     mlspec-bench time writeScript;
           }) benchmark lastEntry withCriterion withTime;

  extractTarball = import ./extractTarball.nix {
                     inherit gnutar runScript withNix;
                   };

  hte-scripts = import ./scripts.nix {
                  inherit coreutils stdenv wget;
                };

  processedPackages = (import ./benchmarkOutputs.nix {
                        inherit bc dumpPackage extractTarball haskellPackages
                                lib parseJSON runScript;
                      });

  c2db-scripts    = import ../cabal2db/scripts.nix         {
                      inherit stdenv nix jq;
                      inherit (haskellPackages) cabal-install;
                    };

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript withNix;
                      inherit (haskellPackages) cabal-install;
                    };

  dumpPackage = import ./dumpPackage.nix {
                  inherit dumpToNix gnutar lib runScript withNix;
                };

  dumpToNix = import ./dumpToNix.nix {
                inherit benchmark c2db-scripts parseJSON runScript withNix;
              };

  testPackageNames     = [ "list-extras" ];

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

  recurrent-clustering = import ../packages/recurrent-clustering {
                           inherit order-deps ML4HSFE annotatedb;
                         };

  downloadAndDump      = import ./downloadAndDump.nix {
                           inherit dumpToNix downloadToNix;
                         };

  assertMsg            = cond: msg:
                           builtins.addErrorContext msg (assert cond; cond);

  shuffledList         = import ./shufflePackages.nix {
                           inherit coreutils pv runScript wget withNix
                                   writeScript;
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
