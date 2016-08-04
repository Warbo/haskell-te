# Custom definitions
self: super:

with builtins; with super.lib;

rec {
  inherit (callPackage ./dumping.nix {})
          dump-package;

  inherit (callPackage ../annotatedb {})
          annotateAsts dumpAndAnnotate;

  inherit (callPackage ./runBenchmark.nix {})
          benchmark checkHsEnv lastEntry withCriterion withTime;

  inherit (callPackage ./benchmarkOutputs.nix {})
          processPackage processPackages;

  inherit (callPackage ./nixFromCabal.nix {})
          nixFromCabal nixedHsPkg;

  inherit (callPackage ./cluster.nix {})
          cluster nixRecurrentClusteringScript recurrentClusteringScript;

  inherit (callPackage ./test-defs.nix {})
          checkPlot runTestInDrv testAll testDbg testMsg testPackages testRec
          testRun testWrap;

  inherit (plotResults)
          mkTbl;

  # These provide executables
  inherit (haskellPackages)
          AstPlugin getDeps ML4HSFE mlspec mlspec-bench reduce-equations;

  annotate             = callPackage ./annotate.nix           {};
  annotateAstsScript   = callPackage ./annotateAstsScript.nix {};
  buildPackage         = callPackage ./buildPackage.nix       {
                           inherit (haskellPackages) cabal2nix cabal-install;
                         };
  downloadAndDump      = callPackage ./downloadAndDump.nix    {};
  downloadToNix        = callPackage ./downloadToNix.nix      {
                           inherit (haskellPackages) cabal-install;
                         };
  drvFromScript        = callPackage ./drvFromScript.nix      {};
  dumpPackage          = callPackage ./dumpPackage.nix        {};
  dumpToNix            = callPackage ./dumpToNix.nix          {};
  explore              = callPackage ./explore.nix            { self = self; }; # Avoid the Self language
  extractTarball       = callPackage ./extractTarball.nix     {};
  format               = callPackage ./format.nix             {};
  getAritiesScript     = callPackage ./getAritiesScript.nix   {};
  getDepsScript        = callPackage ./getDepsScript.nix      {
                           inherit (haskellPackages) getDeps;
                         };
  getTypesScript       = callPackage ./getTypesScript.nix     {};
  haskellPackages      = callPackage ./haskellPackages.nix    {
                           superHaskellPackages = super.haskellPackages;
                         };
  hte-scripts          = callPackage ./scripts.nix            {};
  importDir            = callPackage ./importDir.nix          {};
  ml4hs                = callPackage ../ml4hs                 {};
  parseJSON            = callPackage ./parseJSON.nix          {};
  plotResults          = callPackage ./plotResults.nix        {};
  plots                = callPackage ./plots.nix              {};
  random               = callPackage ./random.nix             {};
  reduce               = callPackage ./reduce.nix             {};
  runScript            = callPackage ./runScript.nix          {};
  runTypes             = callPackage ./runTypes.nix           {};
  runTypesScript       = callPackage ./runTypesScript.nix     {};
  shuffledList         = callPackage ./shufflePackages.nix    {};
  tabulate             = callPackage ./tabulate.nix           {};
  tagAstsScript        = callPackage ./tagAstsScript.nix      {};
  timeCalc             = callPackage ./timeCalc.nix           {};
  tipBenchmarks        = callPackage ./tipBenchmarks.nix      {};

  assertMsg = cond: msg:
    builtins.addErrorContext "not ok - ${msg}"
                             (assert cond; trace "ok - ${msg}" cond);

  callPackage = super.newScope self;

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

  defaultClusters = [ 1 2 4 ];

  # Nix doesn't handle floats, so use bc
  floatDiv = x: y: runScript { buildInputs = [ self.bc ]; }
                     ''echo "scale=16; ${x}/${y}" | bc > "$out"'';

  havePath = n: any (x: x.prefix == n) nixPath;

  nth = n: lst:
    assert ourCheck "Given integer '${toJSON n}'" (isInt  n);
    assert ourCheck "Expecting list, given '${typeOf lst}'" (isList lst);
    assert ourCheck "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
                 (n <= length lst);
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  ourCheck = msg: cond: builtins.addErrorContext msg (assert cond; cond);

  runWeka = callPackage (if havePath "runWeka"
                            then <runWeka>
                            else ../packages/runWeka) {};

  storeResult = self.writeScript "store-result" ''
    set -e
    RESULT=$(nix-store --add "$1")
    printf '%s' "$RESULT" > "$out"
  '';

  strip = s: let unpre = removePrefix "\n" (removePrefix " " s);
                 unsuf = removeSuffix "\n" (removeSuffix " " unpre);
              in if unsuf == s
                    then s
                    else strip unsuf;

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
}
