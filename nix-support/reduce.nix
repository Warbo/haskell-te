{ benchmark, checkFailures, explore, haskellPackages, lib, parseJSON,
  reduce-equations, runScript, writeScript }:
with builtins;
with lib;

rec {

script = writeScript "reduce-equations" "reduce-equations";

mkCat = inputs: "cat " + concatStringsSep " " (map (x: ''"${x}"'') inputs);

doReduce = quick: clusterCount: inputs:
             let allInputs = mkCat inputs;
             in parseJSON (runScript { buildInputs = explore.extractedEnv {
                                         extraHs = [ "reduce-equations" ];
                                       }; } ''
                  set -e
                  export CLUSTERS="${clusterCount}"
                  ${allInputs} | "${benchmark {
                                      inherit quick inputs;
                                      cmd = toString script;
                                  }}" > "$out"
                '');

reduce = { quick, explored }:
  let results = mapAttrs (doReduce quick) explored;
      failed  = checkFailures results;
      result  = { inherit results failed; };
   in result;

}
