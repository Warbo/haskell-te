{ adb-scripts, annotateAstsScript, defaultClusters, getDepsScript,
  getTypesScript, jq, lib, ml4hs, ML4HSFE, nixRecurrentClusteringScript,
  parseJSON, recurrent-clustering, runScript, runTypes, runWeka, storeResult,
  processPackages}:

with builtins;

rec {
  testMsg              = cond: msg:
                           let ok    = "ok - ${msg}";
                               notOk = "not ok - ${msg}";
                            in addErrorContext notOk
                                 (trace (if cond then ok else notOk) cond);

  testPackages = import ./testPackages.nix {
                   inherit adb-scripts annotateAstsScript defaultClusters
                           getDepsScript getTypesScript jq lib ml4hs ML4HSFE
                           nixRecurrentClusteringScript parseJSON
                           recurrent-clustering runScript runTypes runWeka
                           storeResult processPackages;
                 };
}
