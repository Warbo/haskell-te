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

  testMsg = cond: msg: addErrorContext "Testing '${msg}'"
              (assert isBool   cond;
               assert isString msg;
               let code = if cond then "0" else "1";
                in stdenv.mkDerivation {
                     inherit code msg;
                     name = "test-${unsafeDiscardStringContext (hashString "sha256" msg)}";
                     buildCommand = ''
                       source $stdenv/setup

                       echo "$msg" > "$out"

                       if [[ "$code" -eq 0 ]]
                       then
                         echo     "ok - $msg"
                       else
                         echo "not ok - $msg"
                       fi

                       exit "$code"
                     '';
                   });

  testDbg = cond: msg: dbg: addErrorContext dbg
              (testMsg cond msg || trace dbg false);

  testPackages = import ./testPackages.nix {
                   inherit annotateAstsScript defaultClusters getDeps
                           getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                           nixRecurrentClusteringScript parseJSON
                           recurrent-clustering runScript runTypes runWeka
                           storeResult processPackages utillinux;
                 };
}
