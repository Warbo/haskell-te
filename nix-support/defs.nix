# Custom definitions; most functions, values, etc. are imported here and passed
# to their users via 'callPackage'
self: super:

with builtins; with super.lib;

rec {
  inherit (callPackage ./runBenchmark.nix {})
          benchmark checkHsEnv lastEntry withCriterion withTime;

  inherit (callPackage ./benchmarkOutputs.nix {})
          processPackage processPackages;

  inherit (callPackage ./nixFromCabal.nix {})
          nixFromCabal nixedHsPkg;

  inherit (callPackage ./test-defs.nix {})
          runTestInDrv testAll testDbg testDrvString testFiles testMsg
          testPackages testRec testRun testWrap;

  inherit (callPackage ./timeout.nix {})
          timeLimSecs memLimKb timeout;

  # Inherit from the result, so that haskellPackages.override works on the
  # available packages, rather than the arguments to this callPackage invocation
  inherit (callPackage ./haskellPackages.nix {
            superHaskellPackages = super.haskellPackages;
          })
          haskellPackages hsOverride;

  # These provide executables
  inherit (haskellPackages)
          AstPlugin GetDeps ML4HSFE mlspec mlspec-bench reduce-equations;

  annotate           = callPackage ./annotate.nix           {};
  annotateAstsScript = callPackage ./annotateAstsScript.nix {};
  cluster            = callPackage ./cluster.nix            {};
  drvFromScript      = callPackage ./drvFromScript.nix      {};
  dumpPackage        = callPackage ./dumpPackage.nix        {};
  dumpToNix          = callPackage ./dumpToNix.nix          {};
  explore            = callPackage ./explore.nix            {};
  extractTarball     = callPackage ./extractTarball.nix     {};
  format             = callPackage ./format.nix             {};
  getAritiesScript   = callPackage ./getAritiesScript.nix   {};
  getTypesScript     = callPackage ./getTypesScript.nix     {};
  importDir          = callPackage ./importDir.nix          {};
  mlspecBench        = callPackage ./mlspecBench.nix        {};
  package            = callPackage ./package.nix            {};
  parseJSON          = callPackage ./parseJSON.nix          {};
  pkgName            = callPackage ./pkgName.nix            {};
  quickspecBench     = callPackage ./quickspecBench.nix     {};
  reduce             = callPackage ./reduce.nix             {};
  runScript          = callPackage ./runScript.nix          {};
  runTypes           = callPackage ./runTypes.nix           {};
  runTypesScript     = callPackage ./runTypesScript.nix     {};
  tagAstsScript      = callPackage ./tagAstsScript.nix      {};
  timeCalc           = callPackage ./timeCalc.nix           {};
  tipBenchmarks      = callPackage ./tipBenchmarks.nix      {};

  buildPackage    = callPackage ./buildPackage.nix
                      { inherit (haskellPackages) cabal2nix cabal-install; };
  downloadToNix   = callPackage ./downloadToNix.nix
                      { inherit (haskellPackages) cabal-install;           };
  getDepsScript   = callPackage ./getDepsScript.nix
                      { inherit (haskellPackages) GetDeps;                 };
  tests           = callPackage ./tests.nix
                      { pkgs = self;                                       };

  annotated = pkgDir:
    let nixed  = import (nixedHsPkg pkgDir null);
        dumped = dumpPackage {
                   quick = true;
                   src   = nixed;
                 };
        ann    = annotate {
                   pkg    = { name = "dummy"; };
                   quick  = true;
                   asts   = dumped.stdout;
                   pkgSrc = nixed;
                 };
        failed = drvFromScript
                   {
                     dumpF = dumped.failed;
                     dumpE = dumped.stderr;
                      annF = ann.failed;
                      annE = ann.stderr;
                   }
                   ''
                     D=$(cat "$dumpF")
                     [[ "x$D" = "xfalse" ]] || {
                       cat "$dumpE" 1>&2
                       echo "Dump failed (failed = '$D')" 1>&2
                       exit 1
                     }

                     A=$(cat "$annF")
                     [[ "x$A" = "xfalse" ]] || {
                       cat "$annE" 1>&2
                       echo "Annotate failed (failed = '$A')" 1>&2
                       exit 1
                     }
                     touch "$out"
                   '';
     in drvFromScript
          {
            inherit failed;
            ann = ann.stdout;
          }
          ''
             cat "$ann" > "$out"
          '';

  callPackage = super.newScope self;

  checkFailures = type: results:
    assert type == "any" || type == "all";
    let names = attrNames results;
        fails = let l = concatMap (n: if isList results."${n}"
                                         then results."${n}"
                                         else [ results."${n}" ]) names;
                 in map (x: x.failed) l;
        bFunc = if type == "any" then any else all;
     in if all isBool fails
           then bFunc id fails
           else drvFromScript { inherit type; inherit fails; } ''
                  COUNT=0
                  FAILS=0
                  for FAIL in $fails
                  do
                    COUNT=$(( COUNT + 1 ))
                    R=$(cat "$FAIL")
                    [[ "x$R" = "xtrue" ]] || FAILS=$(( FAILS + 1 ))
                  done

                  if [[ "x$type" = "xany" ]] && [[ "$FAILS" -gt 0 ]]
                  then
                    echo "true " > "$out"
                    exit
                  fi

                  if [[ "x$type" = "xall" ]] && [[ "$FAILS" -ge "$COUNT" ]]
                  then
                    echo "true" > "$out"
                    exit
                  fi

                  echo "false" > "$out"
                '';

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

  ensureVars = vars: concatStringsSep "\n"
                       (map (v: ''
                                  [[ -n "${"$" + v}" ]] || {
                                    echo "Required variable '${v}' is empty" 1>&2
                                    exit 2
                                  }
                                '')
                            vars);

  haskellPackageNames = self.writeScript
                          "haskell-names"
                          (self.lib.concatStringsSep "\n" (attrNames haskellPackages));

  havePath = n: any (x: x.prefix == n) nixPath;

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
}
