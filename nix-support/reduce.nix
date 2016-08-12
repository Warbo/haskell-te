{ benchmark, checkFailures, drvFromScript, explore, haskellPackages, lib,
  parseJSON, reduce-equations, runScript, stdParts, storeParts, writeScript }:
with builtins;
with lib;

rec {

script = writeScript "reduce-equations" "reduce-equations";

mkCat = inputs: "cat " + concatStringsSep " " (map (x: ''"${x}"'') inputs);

doReduce = quick: clusterCount: inputs:
             let allInputs = mkCat inputs;
              in drvFromScript { inherit inputs;
                                 outputs = stdParts;
                                 buildInputs = explore.extractedEnv {
                                                 extraHs = [ "reduce-equations" ];
                                                }; } ''
                  set -e
                  export CLUSTERS="${clusterCount}"
                  O=$(cat $inputs | "${benchmark {
                                         inherit quick inputs;
                                         cmd = toString script;
                                     }}")
                  ${storeParts}
                '';

reduce = { quick, explored }:
  let results = mapAttrs (doReduce quick) explored;
      failed  = checkFailures results;
      result  = { inherit results failed; };
   in result;

}
