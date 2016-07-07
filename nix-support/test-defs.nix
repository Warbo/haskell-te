{ annotateAstsScript, defaultClusters, getDeps, getDepsScript,
  getTypesScript, jq, lib, ml4hs, ML4HSFE, nixRecurrentClusteringScript,
  parseJSON, recurrent-clustering, runScript, runTypes, runWeka, storeResult,
  processPackages, utillinux}:

with builtins;

rec {
  testMsg = cond: msg:
              let ok    = "ok - ${msg}";
                  notOk = "not ok - ${msg}";
               in addErrorContext notOk
                    (trace (if cond then ok else notOk) cond);

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
