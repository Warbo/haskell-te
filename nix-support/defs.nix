# Custom definitions
self: super:

with builtins; with super.lib;

rec {

  # Use 'dbug foo bar' in place of 'bar' when 'bar' is fragile, tricky, etc. The
  # value of 'foo' will be included in the stack trace in case of an error, and
  # if the environment variable "TRACE" is non-empty it will also be printed out
  # when there's no error
  dbug = info: val:
    let msg = toJSON { inherit info; };
        v   = if getEnv "TRACE" == ""
                 then val
                 else trace info val;
     in addErrorContext msg v;

  # haskellPackages.override ensures dependencies are overridden too
  haskellPackages = callPackage ./haskellPackages.nix {
                      superHaskellPackages = super.haskellPackages;
                    };

  importDir = callPackage ./importDir.nix {};
  runScript = callPackage ./runScript.nix {};

  inherit (callPackage ./dumping.nix {}) dump-package;

  inherit (callPackage ../annotatedb {}) annotateAsts dumpAndAnnotate;

  inherit (self.callPackage ./runBenchmark.nix {
             inherit (explore) build-env;
           }) benchmark lastEntry withCriterion withTime;

  callPackage = super.newScope self;

  runTypesScript     = callPackage ./runTypesScript.nix     {};
  tagAstsScript      = callPackage ./tagAstsScript.nix      {};
  extractTarball     = callPackage ./extractTarball.nix     {};
  reduce             = callPackage ./reduce.nix             {};
  annotate           = callPackage ./annotate.nix           {};
  getTypesScript     = callPackage ./getTypesScript.nix     {};
  getAritiesScript   = callPackage ./getAritiesScript.nix   {};
  annotateAstsScript = callPackage ./annotateAstsScript.nix {};
  getDepsScript      = callPackage ./getDepsScript.nix {
                         inherit (haskellPackages) getDeps;
                       };

  format      = callPackage ./format.nix {};
  random      = callPackage ./random.nix {};
  hte-scripts = callPackage ./scripts.nix {};

  inherit (callPackage ./benchmarkOutputs.nix {})
          processPackage processPackages;

  inherit (callPackage ./nixFromCabal.nix {})
          nixFromCabal nixedHsPkg;

  explore = callPackage ./explore.nix { inherit self; };

  defaultClusters = [ 1 2 4 ];

  inherit (callPackage ./cluster.nix {})
    cluster nixRecurrentClusteringScript recurrentClusteringScript;

  downloadToNix        = callPackage ./downloadToNix.nix {
                           inherit (haskellPackages) cabal-install;
                         };
  runWeka              = callPackage ../packages/runWeka     {};
  dumpPackage          = callPackage ./dumpPackage.nix       {};
  dumpToNix            = callPackage ./dumpToNix.nix         {};
  drvFromScript        = callPackage ./drvFromScript.nix     {};
  parseJSON            = callPackage ./parseJSON.nix         {};
  ml4hs                = callPackage ../ml4hs                {};
  recurrent-clustering = callPackage ../recurrent-clustering {};
  downloadAndDump      = callPackage ./downloadAndDump.nix   {};

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

  timeCalc     = callPackage ./timeCalc.nix        {};
  shuffledList = callPackage ./shufflePackages.nix {};
  runTypes     = callPackage ./runTypes.nix        {};

  nth = n: lst:
    assert ourCheck "Given integer '${toJSON n}'" (isInt  n);
    assert ourCheck "Expecting list, given '${typeOf lst}'" (isList lst);
    assert ourCheck "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
                 (n <= length lst);
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  inherit (callPackage ./test-defs.nix {})
          checkPlot runTestInDrv testAll testDbg testMsg testPackages testRun
          testWrap;

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

  buildPackage = callPackage ./buildPackage.nix {
                   inherit (haskellPackages) cabal2nix cabal-install;
                 };

  tipBenchmarks = callPackage ./tipBenchmarks.nix {};
  plotResults   = callPackage ./plotResults.nix   {};

  inherit (plotResults) mkTbl;

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ self.bc ]; }
                             ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  tabulate = callPackage ./tabulate.nix {};
  plots    = callPackage ./plots.nix    {};

  # Pull out Haskell packages (e.g. because they provide executables)
  inherit (haskellPackages) AstPlugin getDeps ML4HSFE mlspec mlspec-bench
                            order-deps reduce-equations;
}
