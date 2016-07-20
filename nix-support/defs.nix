# Custom definitions
self: super:

with builtins; with super.lib;

rec {

  # haskellPackages.override ensures dependencies are overridden too
  haskellPackages = import ./haskellPackages.nix {
                      superHaskellPackages = super.haskellPackages;
                      inherit (self) nixFromCabal;
                    };

  inherit (import ./dumping.nix {
             inherit (self) bash haskellPackages gnutar jq lib nix perl procps
                     runCommand stdenv writeScript;
          }) dump-package runScript importDir;

  inherit (import ../annotatedb {
             inherit (self) downloadAndDump getDeps jq lib nix runScript stdenv
                     utillinux;
          }) annotateAsts dumpAndAnnotate;

  inherit (self.callPackage ./runBenchmark.nix {
             inherit (explore) build-env;
           }) benchmark lastEntry withCriterion withTime;

  callPackage = super.newScope self;

  runTypesScript = import ./runTypesScript.nix {
                     inherit (self) haskellPackages jq writeScript;
                   };

  tagAstsScript = import ./tagAstsScript.nix {
                    inherit (self) jq writeScript;
                  };

  extractTarball = import ./extractTarball.nix {
                     inherit (self) gnutar runScript storeResult;
                   };

  reduce = import ./reduce.nix {
             inherit (self) benchmark haskellPackages lib parseJSON reduce-equations runScript writeScript;
           };

  annotate        = self.callPackage ./annotate.nix {};

  getTypesScript = import ./getTypesScript.nix {
                     inherit (self) writeScript;
                   };

  getAritiesScript = import ./getAritiesScript.nix {
                       inherit (self) writeScript;
                     };

  annotateAstsScript = import ./annotateAstsScript.nix {
                         inherit (self) getAritiesScript getTypesScript jq tagAstsScript
                                 writeScript;
                       };

  getDepsScript = import ./getDepsScript.nix {
                    inherit (self) jq utillinux writeScript;
                    inherit (haskellPackages) getDeps;
                  };

  format = import ./format.nix {
             inherit (self) jq parseJSON runScript storeResult;
           };

  random = import ./random.nix {
             inherit (self) jq lib nth parseJSON runScript writeScript;
           };

  hte-scripts = import ./scripts.nix {
                  inherit (self) coreutils stdenv wget;
                };

  inherit (import ./benchmarkOutputs.nix {
            inherit (self) annotate bc buildPackage ourCheck cluster
                    defaultClusters dumpPackage explore
                    extractTarball format haskellPackages jq lib nixedHsPkg
                    nixFromCabal nth parseJSON reduce runScript stdenv
                    storeResult timeCalc writeScript;
          }) processPackage processPackages;

  inherit (import ./nixFromCabal.nix {
             inherit (self) haskellPackages lib stdenv;
           }) nixFromCabal nixedHsPkg;

  explore = import ./explore.nix {
              inherit (self) benchmark ourCheck format haskellPackages jq lib ml4hs
                      parseJSON runScript writeScript;
              inherit self;
            };

  defaultClusters = [ 1 2 4 ];

  inherit (import ./cluster.nix {
             inherit (self) benchmark ML4HSFE parseJSON recurrent-clustering runScript
                     runWeka writeScript;
          }) cluster nixRecurrentClusteringScript recurrentClusteringScript;

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit (self) runScript storeResult;
                      inherit (haskellPackages) cabal-install;
                    };

  runWeka = import ../packages/runWeka {
              inherit (self) jq jre runCommand stdenv weka;
            };

  dumpPackage = import ./dumpPackage.nix {
                  inherit (self) dumpToNix gnutar lib runScript;
                };

  dumpToNix = import ./dumpToNix.nix {
                inherit (self) benchmark dump-package parseJSON runScript;
              };

  parseJSON            = import ./parseJSON.nix {
                           inherit (self) jq runScript writeScript;
                         };

  ml4hs                = import ../ml4hs            {
                           inherit (self) haskellPackages jq mlspec stdenv;
                         };

  recurrent-clustering = import ../recurrent-clustering {
                           inherit (self) jq ML4HSFE nix order-deps stdenv;
                         };

  downloadAndDump      = import ./downloadAndDump.nix {
                           inherit (self) dumpToNix downloadToNix;
                         };

  assertMsg            = cond: msg:
                           builtins.addErrorContext
                             "not ok - ${msg}"
                             (assert cond; trace "ok - ${msg}" cond);

  ourCheck = msg: cond: builtins.addErrorContext msg (assert cond; cond);

  checkStdDev = sd:
    assert ourCheck "isAttrs stddev '${toJSON sd}'"
                 (isAttrs sd);
    assert ourCheck "Stddev '${toJSON sd}' has estPoint"
                 (sd ? estPoint);
    assert ourCheck "Stddev estPoint '${toJSON sd.estPoint}'"
                 (isString sd.estPoint);
    true;

  checkTime = t:
    assert ourCheck "isAttrs '${toJSON t}'"           (isAttrs t);
    assert ourCheck "${toJSON t} has mean"            (t ? mean);
    assert ourCheck "isAttrs '${toJSON t.mean}'"      (isAttrs t.mean);
    assert ourCheck "'${toJSON t.mean}' has estPoint" (t.mean ? estPoint);
    t ? stddev -> ourCheck "Checking stddev" (checkStdDev t.stddev);

  timeCalc = import ./timeCalc.nix {
              inherit (self) bc ourCheck checkStdDev checkTime lib nth parseJSON
                      runScript;
             };

  shuffledList = import ./shufflePackages.nix {
                   inherit (self) coreutils jq parseJSON pv runScript storeResult wget
                           writeScript;
                 };

  runTypes = import ./runTypes.nix        {
               inherit (self) jq runScript runTypesScript storeResult getDeps utillinux;
             };

  nth = n: lst:
    assert ourCheck "Given integer '${toJSON n}'" (isInt  n);
    assert ourCheck "Expecting list, given '${typeOf lst}'" (isList lst);
    assert ourCheck "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
                 (n <= length lst);
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  inherit (import ./test-defs.nix {
            inherit (self) annotateAstsScript buildEnv defaultClusters getDeps
                    getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                    nixRecurrentClusteringScript parseJSON processPackages
                    recurrent-clustering runScript runTypes runWeka stdenv
                    storeResult utillinux;
          })
          testAll testDbg testMsg testPackages;

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

  storeResult = self.writeScript "store-result" ''
      set -e
      RESULT=$(nix-store --add "$1")
      printf '%s' "$RESULT" > "$out"
    '';

  buildPackage = import ./buildPackage.nix {
                   inherit (self) benchmark parseJSON runScript writeScript;
                   inherit (haskellPackages) cabal2nix cabal-install;
                 };

  tipBenchmarks = import ./tipBenchmarks.nix {
                    inherit (self) bash defaultClusters haskellPackages
                            nixFromCabal processPackage racket runScript
                            stdenv storeResult writeScript;
                  };

  plotResults = import ./plotResults.nix {
                  inherit (self) ourCheck gnuplot lib runScript storeResult writeScript;
                };
  inherit (plotResults) mkTbl;

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ self.bc ]; }
                             ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  tabulate = import ./tabulate.nix {
               inherit (self) ourCheck checkTime lib processPackages;
             };

  plots = import ./plots.nix {
            inherit (self) ourCheck defaultClusters lib parseJSON plotResults runScript
                    shuffledList tabulate;
          };

  checkPlot = plot:
    let w      = "640";
        h      = "480";
        exists = testMsg (pathExists plot) "Checking if plot '${plot}' exists";
        dims   = testMsg (parseJSON (runScript { buildInputs = [ self.file self.jq ]; } ''
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

  # Pull out Haskell packages (e.g. because they provide executables)
  inherit (self.haskellPackages) AstPlugin getDeps ML4HSFE mlspec mlspec-bench
                                 order-deps reduce-equations;
}
