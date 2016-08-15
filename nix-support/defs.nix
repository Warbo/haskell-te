# Custom definitions; most functions, values, etc. are imported here and passed
# to their users via 'callPackage'
self: super:

with builtins; with super.lib;

rec {
  inherit (callPackage ./dumping.nix {})
          dump-package;

  inherit (callPackage ./runBenchmark.nix {})
          benchmark checkHsEnv lastEntry withCriterion withTime;

  inherit (callPackage ./benchmarkOutputs.nix {})
          processPackage processPackages;

  inherit (callPackage ./nixFromCabal.nix {})
          nixFromCabal nixedHsPkg;

  inherit (callPackage ./cluster.nix {})
          cluster nixRecurrentClusteringScript recurrentClusteringScript;

  inherit (callPackage ./test-defs.nix {})
          checkPlot runTestInDrv testAll testDbg testDrvString testFiles testMsg
          testPackages testRec testRun testWrap;

  inherit (plotResults)
          mkTbl;

  inherit (callPackage ./timeout.nix {})
          timeLimSecs memLimKb timeout;

  # These provide executables
  inherit (haskellPackages)
          AstPlugin GetDeps ML4HSFE mlspec mlspec-bench reduce-equations;

  annotate             = callPackage ./annotate.nix           {};
  annotateAsts         = callPackage ./annotateAsts.nix       {};
  annotateAstsScript   = callPackage ./annotateAstsScript.nix {};
  buildPackage         = callPackage ./buildPackage.nix       {
                           inherit (haskellPackages) cabal2nix cabal-install;
                         };
  downloadAndDump      = callPackage ./downloadAndDump.nix    {};
  downloadToNix        = callPackage ./downloadToNix.nix      {
                           inherit (haskellPackages) cabal-install;
                         };
  drvFromScript        = callPackage ./drvFromScript.nix      {};
  dumpAndAnnotate      = callPackage ./dumpAndAnnotate.nix    {};
  dumpPackage          = callPackage ./dumpPackage.nix        {};
  dumpToNix            = callPackage ./dumpToNix.nix          {};
  explore              = callPackage ./explore.nix            { self = self; }; # Avoid the Self language
  extractTarball       = callPackage ./extractTarball.nix     {};
  format               = callPackage ./format.nix             {};
  getAritiesScript     = callPackage ./getAritiesScript.nix   {};
  getDepsScript        = callPackage ./getDepsScript.nix      {
                           inherit (haskellPackages) GetDeps;
                         };
  getTypesScript       = callPackage ./getTypesScript.nix     {};
  haskellPackages      = callPackage ./haskellPackages.nix    {
                           superHaskellPackages = super.haskellPackages;
                         };
  importDir            = callPackage ./importDir.nix          {};
  ml4hs                = callPackage ../ml4hs                 {};
  parseJSON            = callPackage ./parseJSON.nix          {};
  pkgName              = callPackage ./pkgName.nix            {};
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
  tests                = callPackage ./tests.nix              { pkgs = self; };
  timeCalc             = callPackage ./timeCalc.nix           {};
  tipBenchmarks        = callPackage ./tipBenchmarks.nix      {};

  assertMsg = cond: msg:
    builtins.addErrorContext "not ok - ${msg}"
                             (assert cond; trace "ok - ${msg}" cond);

  callPackage = super.newScope self;

  checkFailures = results:
    let names = attrNames results;
        fails = let l = concatMap (n: if isList results."${n}"
                                         then results."${n}"
                                         else [ results."${n}" ]) names;
                 in map (x: x.failed) l;
     in if all isBool fails
           then any id fails
           else drvFromScript { inherit fails; } ''
                  for FAIL in $fails
                  do
                    R=$(cat "$FAIL")
                    [[ "x$R" = "xtrue" ]] && continue
                    echo "false" > "$out"
                    exit 0
                  done

                  echo "true" > "$out"
                '';

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

  haskellPackageNames = self.writeScript
                          "haskell-names"
                          (self.lib.concatStringsSep "\n" (attrNames haskellPackages));

  havePath = n: any (x: x.prefix == n) nixPath;

  nth = n: lst:
    assert isInt  n          || abort "Should be int '${toJSON n}'";
    assert isList lst        || abort "Expecting list, given '${typeOf lst}'";
    assert (n <= length lst) || abort "Index '${toJSON n}' in bounds '${toJSON (length lst)}'";
    if n == 1
       then head lst
       else nth (n - 1) (tail lst);

  ourCheck = msg: cond: cond || abort msg;

  runWeka = callPackage (if havePath "runWeka"
                            then <runWeka>
                            else ../packages/runWeka) {};

  stdParts = [ "failed" "out" "stderr" "stdout" "time" ];

  storeParts = ''
    echo "$O" > "$out"

    SO=$(echo "$O" | jq -r ".stdout")
    cp "$SO" "$stdout"

    SE=$(echo "$O" | jq -r ".stderr")
    cp "$SE" "$stderr"

    echo "$O" | jq -r ".time" > "$time"

    echo "$O" | jq -r ".failed" > "$failed"
  '';

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
