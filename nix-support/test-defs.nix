{ buildEnv, callPackage, dbug, drvFromScript, file, jq, lib, parseJSON,
  runScript, stdenv, writeScript}:

with builtins;
with lib;

# Each test is a derivation, which we collect up and present for evaluation

rec {
  assertList = l: dbug "assertList ${toJSON l}"
                    (assert isList l; true);

  assertTest = t: dbug "assertTest ${toJSON t}"
                    (assert isBool t || isAttrs t; true);

  areTests   = ts: dbug "areTests ${toJSON ts}"
                     (assertList ts && all assertTest ts);

  stripStr   = stringAsChars (c: if elem c (upperChars ++ lowerChars)
                                    then c
                                    else "");

  testAll = tests: dbug "testAll ${toJSON tests}"
                     (assert areTests tests;
                      testWrap tests "Collected tests");

  # Create a new test out of other ones; this lets us assign a 'higher level'
  # meaning to some results, e.g. 'tests' might be 'foo contains x',
  # 'foo contains y', 'foo contains z', whilst 'msg' might be
  # 'foo has all required fields'
  testWrap = tests: msg:
               dbug "testWrap ${toJSON { inherit tests msg; }}"
                 (assert areTests tests;
                  # If there are any raw booleans in 'tests', turn them into
                  # trivial derivations
                  let testDrvs = map (t: if isBool t
                                            then testMsg t "Unknown test"
                                            else assert isAttrs t; t)
                                     tests;
                   in testRun msg null { buildInputs = testDrvs; } ''
                        # Always pass; failure is triggered by our buildInputs
                        exit 0
                      '');

  testMsg = cond: msg:
              addErrorContext "testMsg ${toJSON { inherit cond msg; }}"
                (assert isBool   cond;
                 assert isString msg;
                 testDbg cond msg null);

  testDbg = cond: msg: dbg:
              addErrorContext "testDbg ${toJSON { inherit cond msg dbg; }}"
              (assert isBool cond;
               testRun msg dbg {} ''
                 exit ${if cond then "0" else "1"}
               '');

  testRun = msg: dbg: envOverride: script:
            let info       = toJSON
                               ({ inherit msg; } // (if dbg == null
                                                        then {}
                                                        else { inherit dbg; }));
                err        = x: trace "Testing ${info}"
                                  (dbug "Testing ${info}" x);
                scriptFile = writeScript "test-script" script;
                hash       = unsafeDiscardStringContext (stripStr msg);
                env        = {
                  inherit info msg scriptFile;
                  name         = "test-${hash}";
                  passAsFile   = [ "info" ];
                  buildCommand = ''
                    source $stdenv/setup

                    echo "# $msg" >> "$out"
                    echo "true"   >> "$out"

                    if "${scriptFile}"
                    then
                      echo     "ok - $msg"
                      exit 0
                    else
                      echo "not ok - $msg"
                      cat "$infoPath" 1>&2
                      exit 1
                    fi
                  '';
                };
             in err (assert isString msg;
                     stdenv.mkDerivation (env // envOverride));

  checkPlot = plot:
    let w      = "640";
        h      = "480";
        exists = testMsg (pathExists plot) "Checking if plot '${plot}' exists";
        dims   = testMsg
                   (parseJSON
                     (runScript { buildInputs = [ file jq ]; } ''
                       set -e
                       echo "Checking '${plot}' bigger than ${w}x${h}" 1>&2
                       GEOM=$(file "${plot}" | # filename: foo, W x H, baz
                              cut -d : -f 2  | # foo, W x H,baz
                              cut -d , -f 2  ) # W x H
                       W=$(echo "$GEOM" | cut -d x -f 1)
                       H=$(echo "$GEOM" | cut -d x -f 2)

                       echo "Checking '$W'x'$H' against '${w}'x'${h}'" 1>&2
                       jq -n --argjson width  "$W" \
                             --argjson height "$H" \
                             '$width >= ${w} and $height >= ${h}' > "$out"
                     ''))
                   "Plot dimensions sufficient (indicates GNUPlot succeeded)";
     in testWrap [
          (plot != null)
          exists
          dims
        ] "Checking plot ${toJSON plot}";

  testPackages = callPackage ./testPackages.nix {};

  # Build the contents of a Nix file, using nix-build. This lets us use Nix to
  # write our tests, whilst maintaining an eval-time/build-time separation.
  runTestInDrv = testPath: extraArgs:
    let allArgs = ["(import ./nix-support {})"] ++ extraArgs;
        argStr  = concatStringsSep " " allArgs;
     in drvFromScript { inherit testPath argStr; } ''
          cd "${./..}"
          nix-build --no-out-link -E "import ./$testPath $argStr" || exit 1
          touch "$out"
        '';
}
