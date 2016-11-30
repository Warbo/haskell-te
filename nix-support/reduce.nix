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

doReduce = quick: clusterCount: inputs:
             drvFromScript { inherit inputs;
                             outputs = stdParts;
                             buildInputs = explore.extractedEnv {}; } ''
               set -e

               ${preamble}

               export CLUSTERS="${clusterCount}"
               O=$(getEqs | "${runCmd {
                               inherit quick inputs;
                               cmd = "${reduce-equations}/bin/reduce-equations";
                             }}")
               ${storeParts}
             '';

reduce = { quick, explored }:
  let results = mapAttrs (doReduce quick) explored;
      failed  = checkFailures "any" results;
      result  = { inherit results failed; };
   in result;
}
