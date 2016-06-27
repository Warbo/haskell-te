# Custom definitions
{ fetchurl, bash, bc, buildEnv, coreutils, file, gnuplot, gnutar,
  haskellPackages, jq, jre, lib, nix, perl, procps, pv, runCommand, stdenv,
  time, utillinux, weka, wget, writeScript }:

with builtins; with lib;
let defs = rec {
  inherit (import ./dumping.nix {
             inherit haskellPackages gnutar jq lib nix perl procps runCommand
                     stdenv writeScript;
          }) dump-package runScript importDir;

  inherit (import ../annotatedb {
             inherit downloadAndDump getDeps jq lib nix runScript stdenv
                     utillinux;
          }) annotateAsts dumpAndAnnotate;

  inherit (import ./runBenchmark.nix {
             inherit bash check coreutils jq lib
                     mlspec-bench time writeScript;
             inherit (explore) build-env;
           }) benchmark lastEntry withCriterion withTime;

  runTypesScript = import ./runTypesScript.nix {
                     inherit haskellPackages jq writeScript;
                   };

  tagAstsScript = import ./tagAstsScript.nix {
                    inherit jq writeScript;
                  };

  extractTarball = import ./extractTarball.nix {
                     inherit gnutar runScript storeResult;
                   };

  reduce = import ./reduce.nix {
             inherit benchmark haskellPackages lib parseJSON reduce-equations runScript writeScript;
           };

  annotate        = import ./annotate.nix        {
                      inherit annotateAstsScript benchmark getDeps
                              getDepsScript jq parseJSON runScript
                              runTypesScript utillinux writeScript;
                    };

  getTypesScript = import ./getTypesScript.nix {
                     inherit writeScript;
                   };

  getAritiesScript = import ./getAritiesScript.nix {
                       inherit writeScript;
                     };

  annotateAstsScript = import ./annotateAstsScript.nix {
                         inherit getAritiesScript getTypesScript jq tagAstsScript
                                 writeScript;
                       };

  getDepsScript = import ./getDepsScript.nix {
                    inherit jq utillinux writeScript;
                    inherit (haskellPackages) getDeps;
                  };

  format = import ./format.nix {
             inherit jq parseJSON runScript storeResult;
           };

  random = import ./random.nix {
             inherit jq lib nth parseJSON runScript writeScript;
           };

  hte-scripts = import ./scripts.nix {
                  inherit coreutils stdenv wget;
                };

  inherit (import ./benchmarkOutputs.nix {
            inherit annotate bc buildPackage check cluster
                    defaultClusters dumpPackage explore
                    extractTarball format haskellPackages jq lib nixFromCabal
                    nth parseJSON reduce runScript stdenv storeResult timeCalc
                    writeScript;
          }) processPackage processPackages;

  nixFromCabal = import ./nixFromCabal.nix {
                   inherit haskellPackages lib stdenv;
                 };

  explore = import ./explore.nix {
              inherit benchmark check format haskellPackages jq lib ml4hs
                      parseJSON runScript writeScript;
              defs = import <nixpkgs> {} // defs;
            };

  defaultClusters = [ 1 2 4 ];

  inherit (import ./cluster.nix {
             inherit benchmark ML4HSFE parseJSON recurrent-clustering runScript
                     runWeka writeScript;
          }) cluster nixRecurrentClusteringScript recurrentClusteringScript;

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript storeResult;
                      inherit (haskellPackages) cabal-install;
                    };

  runWeka = import ../packages/runWeka {
              inherit jq jre runCommand stdenv weka;
            };

  dumpPackage = import ./dumpPackage.nix {
                  inherit dumpToNix gnutar lib runScript;
                };

  dumpToNix = import ./dumpToNix.nix {
                inherit benchmark dump-package parseJSON runScript;
              };

  parseJSON            = import ./parseJSON.nix {
                           inherit jq runScript writeScript;
                         };

  ml4hs                = import ../ml4hs            {
                           inherit haskellPackages jq mlspec stdenv;
                         };

  recurrent-clustering = import ../recurrent-clustering {
                           inherit jq ML4HSFE nix order-deps stdenv;
                         };

  downloadAndDump      = import ./downloadAndDump.nix {
                           inherit dumpToNix downloadToNix;
                         };

  assertMsg            = cond: msg:
                           builtins.addErrorContext
                             "not ok - ${msg}"
                             (assert cond; trace "ok - ${msg}" cond);

  check = msg: cond: builtins.addErrorContext msg (assert cond; cond);

  checkStdDev = sd:
    assert check "isAttrs stddev '${toJSON sd}'"
                 (isAttrs sd);
    assert check "Stddev '${toJSON sd}' has estPoint"
                 (sd ? estPoint);
    assert check "Stddev estPoint '${toJSON sd.estPoint}'"
                 (isString sd.estPoint);
    true;

  checkTime = t:
    assert check "isAttrs '${toJSON t}'"           (isAttrs t);
    assert check "${toJSON t} has mean"            (t ? mean);
    assert check "isAttrs '${toJSON t.mean}'"      (isAttrs t.mean);
    assert check "'${toJSON t.mean}' has estPoint" (t.mean ? estPoint);
    t ? stddev -> check "Checking stddev" (checkStdDev t.stddev);

  timeCalc = import ./timeCalc.nix {
              inherit bc check checkStdDev checkTime lib nth parseJSON
                      runScript;
             };

  shuffledList = import ./shufflePackages.nix {
                   inherit coreutils jq parseJSON pv runScript storeResult wget
                           writeScript;
                 };

  runTypes = import ./runTypes.nix        {
               inherit jq runScript runTypesScript storeResult;
             };

  nth = n: lst:
    assert check "Given integer '${toJSON n}'" (isInt  n);
    assert check "Expecting list, given '${typeOf lst}'" (isList lst);
    assert check "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
                 (n <= length lst);
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  inherit (import ./test-defs.nix {
            inherit annotateAstsScript defaultClusters
                    getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                    nixRecurrentClusteringScript parseJSON
                    recurrent-clustering runScript runTypes runWeka storeResult
                    processPackages;
          })
          testDbg testMsg testPackages;

  uniq =
    let uniq' = list: acc:
          seq acc (if list == []
                      then acc
                      else let x  = head   list;
                               xs = drop 1 list;
                            in uniq' xs (acc ++ (if elem x xs
                                                    then []
                                                    else [x])));
     in l: uniq' l [];

  storeResult = writeScript "store-result" ''
      set -e
      RESULT=$(nix-store --add "$1")
      printf '%s' "$RESULT" > "$out"
    '';

  buildPackage = import ./buildPackage.nix {
                   inherit benchmark parseJSON runScript writeScript;
                   inherit (haskellPackages) cabal2nix cabal-install;
                 };

  tipBenchmarks = import ./tipBenchmarks.nix {
                    inherit defaultClusters haskellPackages nixFromCabal
                            processPackage runScript storeResult writeScript;
                  };

  plotResults = import ./plotResults.nix {
                  inherit check gnuplot lib runScript storeResult writeScript;
                };
  inherit (plotResults) mkTbl;

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ bc ]; }
                             ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  tabulate = import ./tabulate.nix {
               inherit check checkTime lib processPackages;
             };

  plots = import ./plots.nix {
            inherit check defaultClusters lib parseJSON plotResults runScript
                    shuffledList tabulate;
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
     in plot != null && (exists && dims);

  # Include our overridden Haskell packages
  inherit haskellPackages;

  # Pull out Haskell packages (e.g. because they provide executables)
  inherit (haskellPackages) AstPlugin getDeps ML4HSFE mlspec mlspec-bench
                            order-deps reduce-equations;
}; in defs
