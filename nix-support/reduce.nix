{ runCmd, checkFailures, drvFromScript, explore, haskellPackages, lib,
  reduce-equations, stdParts, storeParts, writeScript }:
with builtins;
with lib;

rec {

preamble = ''
  set -e

  function getEqs {
    for F in $inputs
    do
      jq '.[]' < "$F"
    done | jq -s '.'
  }
'';

doReduce = clusterCount: inputs:
             drvFromScript { inherit inputs;
                             outputs = stdParts;
                             buildInputs = explore.extractedEnv {}; } ''
               set -e

               ${preamble}

               export CLUSTERS="${clusterCount}"
               O=$(getEqs | "${runCmd {
                               inherit inputs;
                               cmd = "${reduce-equations}/bin/reduce-equations";
                             }}")
               ${storeParts}
             '';

reduce = { explored }:
  let results = mapAttrs doReduce explored;
      failed  = checkFailures "any" results;
      result  = { inherit results failed; };
   in result;
}
