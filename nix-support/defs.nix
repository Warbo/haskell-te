# Custom definitions
{ bash, bc, buildEnv, coreutils, file, gnuplot, gnutar, haskellPackages, jq,
  lib, nix, pv, real, runCommand, stdenv, time, utillinux, wget, writeScript }:

with builtins; with lib;
rec {
  inherit coreutils;

  inherit (import ./dumping.nix {
             inherit stdenv haskellPackages nix gnutar jq lib runCommand
                     writeScript;
          }) dump-package runScript importDir withNix;

  inherit (import ../annotatedb {
             inherit downloadAndDump getDeps jq lib nix runScript stdenv
                     utillinux withNix;
          }) adb-scripts annotateAsts dumpAndAnnotate;

  inherit (import ./runBenchmark.nix {
             inherit bash coreutils explore-theories jq lib
                     mlspec-bench time writeScript;
           }) benchmark lastEntry withCriterion withTime;

  extractTarball = import ./extractTarball.nix {
                     inherit gnutar runScript withNix;
                   };

  annotate        = import ./annotate.nix        {
                      inherit adb-scripts benchmark jq parseJSON runScript
                              withNix;
                    };


  hte-scripts = import ./scripts.nix {
                  inherit coreutils stdenv wget;
                };

  benchmarkPackages = (import ./benchmarkOutputs.nix {
                        inherit annotate bc buildPackage cluster dumpPackage
                                explore extractTarball haskellPackages jq lib
                                parseJSON runScript timeCalc; });

  processedPackages = benchmarkPackages { clusters = defaultClusters; };

  explore = import ./explore.nix {
              inherit benchmark explore-theories lib ml4hs parseJSON runScript
                      withNix writeScript;
            };

  defaultClusters = [ 1 2 4 ];

  cluster = import ./cluster.nix {
              inherit benchmark parseJSON recurrent-clustering runScript withNix;
            };

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript withNix;
                      inherit (haskellPackages) cabal-install;
                    };

  dumpPackage = import ./dumpPackage.nix {
                  inherit dumpToNix gnutar lib runScript withNix;
                };

  dumpToNix = import ./dumpToNix.nix {
                inherit benchmark dump-package parseJSON runScript
                        withNix;
              };

  parseJSON            = import ./parseJSON.nix {
                           inherit jq runScript writeScript;
                         };

  explore-theories     = import ../packages/explore-theories {
                           inherit stdenv;
                         };

  ml4hs                = import ../ml4hs            {
                           inherit haskellPackages jq mlspec stdenv;
                         };

  recurrent-clustering = import ../recurrent-clustering {
                           inherit adb-scripts jq ML4HSFE nix order-deps stdenv;
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

  runTypes        = import ./runTypes.nix        {
                      inherit adb-scripts jq storeResult runScript withNix;
                    };

  # FIXME: Move test-related definitions to a separate defs file
  testPackages  = import ./testPackages.nix {
                    inherit adb-scripts defaultClusters explore-theories jq lib
                            ml4hs ML4HSFE parseJSON processedPackages
                            recurrent-clustering runScript runTypes storeResult
                            withNix;
                  };

  # FIXME: Replace other occurrences of nix-store with storeResult
  storeResult = writeScript "store-result" ''
    set -e
    RESULT=$(nix-store --add "$1")
    printf '%s' "$RESULT" > "$out"
  '';

  buildPackage = import ./buildPackage.nix {
                   inherit benchmark parseJSON runScript withNix;
                   inherit (haskellPackages) cabal2nix cabal-install;
                 };

  inherit (import ./plotResults.nix {
            inherit gnuplot lib runScript storeResult withNix writeScript;
          })
          mkTbl plotSizeVsThroughput;

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ bc ]; }
                             ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  timeCalc = import ./timeCalc.nix {
               inherit bc lib;
             };

  checkPlot = plot: let w = "640"; h = "480"; in
    assertMsg (pathExists plot) "Checking if plot '${plot}' exists" &&
    assertMsg (parseJSON (runScript { buildInputs = [ file jq ]; } ''
      set -e
      echo "Checking '${plot}' bigger than ${w}x${h}" 1>&2
      GEOM=$(file "${plot}" | # filename: foo, W x H, baz
             cut -d : -f 2  | # bar, W x H,baz
             cut -d , -f 2  ) # W x H
             W=$(echo "$GEOM" | cut -d x -f 1)
             H=$(echo "$GEOM" | cut -d x -f 2)

             echo "Checking '$W'x'$H' against '${w}'x'${h}'" 1>&2
             jq -n --argjson width  "$W" \
                   --argjson height "$H" \
                   '$width >= ${w} and $height >= ${h}' > "$out"
  '')) "Plot has sufficient dimensions (indicates GNUPlot succeeded)";

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
