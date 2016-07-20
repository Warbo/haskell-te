{ annotateAstsScript, buildEnv, defaultClusters, getDeps, getDepsScript,
  getTypesScript, jq, lib, ml4hs, ML4HSFE, nixRecurrentClusteringScript,
  parseJSON, recurrent-clustering, runScript, runTypes, runWeka, stdenv,
  storeResult, processPackages, utillinux}:

with builtins;

# Each test is a derivation, which we collect up and present for evaluation

rec {
  testAll = tests:
              assert isList tests;
              assert all isAttrs tests;
              buildEnv {
                name = "test-set";
                paths = tests;
              };

  testMsg = cond: msg: testDbg cond msg null;

  testDbg = cond: msg: dbg:
              assert isBool cond;
              testRun msg dbg {} ''
                exit ${if cond then "0" else "1"}
              '';

  testRun = msg: dbg: env: script:
            let err = x:
                  (if dbg == null
                      then (y: y)
                      else addErrorContext dbg)
                    (addErrorContext "Testing '${msg}'" x);
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

  testPackages = import ./testPackages.nix {
                   inherit annotateAstsScript defaultClusters getDeps
                           getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                           nixRecurrentClusteringScript parseJSON
                           recurrent-clustering runScript runTypes runWeka
                           storeResult processPackages utillinux;
                 };
}
