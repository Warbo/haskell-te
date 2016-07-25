{ annotateAstsScript, buildEnv, dbug, defaultClusters, file, getDeps,
  getDepsScript, getTypesScript, jq, lib, ml4hs, ML4HSFE,
  nixRecurrentClusteringScript, parseJSON, recurrent-clustering, runScript,
  runTypes, runWeka, stdenv, storeResult, processPackages, utillinux,
  writeScript}:

with builtins;

# Each test is a derivation, which we collect up and present for evaluation

rec {
  assertList = l: dbug "assertList ${toJSON l}"
                    (assert isList l; true);

  assertTest = t: dbug "assertTest ${toJSON t}"
                    (assert isBool t || isAttrs t; true);

  areTests   = ts: dbug "areTests ${toJSON ts}"
                     (assertList ts && all assertTest ts);

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

  testRun = msg: dbg: env: script:
            let info = { inherit msg; } // (if dbg == null
                                               then {}
                                               else { inherit dbg; });
                err  = x: trace "Testing ${toJSON info}" (dbug "Testing ${toJSON info}" x);
                scriptFile = writeScript "test-script" script;
             in err (assert isString msg;
                     stdenv.mkDerivation ({
                       inherit dbg msg scriptFile;
                       name = "test-${unsafeDiscardStringContext (hashString "sha256" msg)}";
                       buildCommand = ''
                         source $stdenv/setup

                         echo "$msg" > "$out"

                         if "${scriptFile}"
                         then
                           echo     "ok - $msg"
                           exit 0
                         else
                           echo "not ok - $msg"
                           ${if dbg == null then ''echo "$dbg" 1>&2''
                                            else ""}
                           exit 1
                         fi
                       '';
                     } // env));

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

  testPackages = import ./testPackages.nix {
                   inherit annotateAstsScript defaultClusters getDeps
                           getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                           nixRecurrentClusteringScript parseJSON
                           recurrent-clustering runScript runTypes runWeka
                           storeResult processPackages utillinux;
                 };
}
