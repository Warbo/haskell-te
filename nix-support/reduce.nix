{ benchmark, checkFailures, drvFromScript, explore, haskellPackages, lib,
  reduce-equations, stdParts, storeParts, writeScript }:
with builtins;
with lib;

rec {

preamble = ''
  set -e

  function getEqs {
    for F in $inputs
    do
      jq -c '.[]' < "$F"
    done
  }
'';

doReduce = quick: clusterCount: inputs:
             drvFromScript { inherit inputs;
                             outputs = stdParts;
                             buildInputs = explore.extractedEnv {
                                             extraPkgs = [ reduce-equations ];
                                           }; } ''
               set -e

               ${preamble}

               export CLUSTERS="${clusterCount}"
               O=$(getEqs | "${benchmark {
                               inherit quick inputs;
                               cmd = "reduce-equations";
                             }}")
               ${storeParts}
             '';

reduce = { quick, explored }:
  let results = mapAttrs (doReduce quick) explored;
      failed  = checkFailures "any" results;
      result  = { inherit results failed; };
   in result;
}
