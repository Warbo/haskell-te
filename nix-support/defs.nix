# Custom definitions
{ fetchurl, bash, bc, buildEnv, buildPythonPackage, coreutils, file, gnuplot, gnutar,
  haskellPackages, jq, lib, nix, pv, pythonPackages,
  real, runCommand, stdenv, time, utillinux, wget, writeScript }:

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
                     inherit gnutar runScript storeResult withNix;
                   };

  annotate        = import ./annotate.nix        {
                      inherit adb-scripts benchmark jq parseJSON runScript
                              withNix;
                    };

  format = import ./format.nix {
             inherit jq parseJSON runScript storeResult;
           };

  hte-scripts = import ./scripts.nix {
                  inherit coreutils stdenv wget;
                };

  processPackages = (import ./benchmarkOutputs.nix {
                       inherit annotate bc buildPackage check cluster
                               dumpPackage explore extractTarball format
                               haskellPackages jq lib nth parseJSON runScript
                               timeCalc; });

  defaultPackages = processPackages { clusters = defaultClusters; };

  explore = import ./explore.nix {
              inherit benchmark check explore-theories format lib ml4hs
                      parseJSON runScript withNix writeScript;
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
                           builtins.addErrorContext
                             "not ok - ${msg}"
                             (assert cond; trace "ok - ${msg}" cond);

  testMsg              = cond: msg:
                           let ok    = "ok - ${msg}";
                               notOk = "not ok - ${msg}";
                           in builtins.addErrorContext notOk
                                (trace (if cond then ok else notOk) cond);

  check = msg: cond: builtins.addErrorContext msg (assert cond; cond);

  timeCalc = import ./timeCalc.nix {
              inherit bc check lib nth parseJSON runScript;
             };

  shuffledList         = import ./shufflePackages.nix {
                           inherit coreutils pv runScript wget withNix
                                   writeScript;
                         };

  runTypes        = import ./runTypes.nix        {
                      inherit adb-scripts jq storeResult runScript withNix;
                    };

  nth = n: lst:
    assert check "Given integer '${toJSON n}'" (isInt  n);
    assert check "Expecting list, given '${typeOf lst}'" (isList lst);
    assert check "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
                 (n <= length lst);
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  # FIXME: Move test-related definitions to a separate defs file
  testPackages  = import ./testPackages.nix {
                    inherit adb-scripts defaultClusters explore-theories jq lib
                            ml4hs ML4HSFE parseJSON defaultPackages
                            recurrent-clustering runScript runTypes storeResult
                            withNix processPackages;
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

  plotResults = import ./plotResults.nix {
                  inherit gnuplot lib runScript storeResult withNix writeScript;
                };
  inherit (plotResults) mkTbl;

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ bc ]; }
                             ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  tabulate = import ./tabulate.nix {
               inherit lib processPackages;
             };

  plots = import ./plots.nix {
            inherit defaultClusters plotResults tabulate;
          };

  checkPlot = plot:
    let w      = "640";
        h      = "480";
        exists = testMsg (pathExists plot) "Checking if plot '${plot}' exists";
        dims   = testMsg (parseJSON (runScript { buildInputs = [ file jq ]; } ''
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
     in trace "Checking plot ${plot}" (exists && dims);

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
