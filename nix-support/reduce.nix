{ benchmark, haskellPackages, lib, parseJSON, reduce-equations, runScript, writeScript }:
with builtins;
with lib;

rec {

script = writeScript "reduce-equations" "reduce-equations";

doReduce = quick: clusterCount: f:
             parseJSON (runScript env ''
               set -e
               export CLUSTERS="${clusterCount}"
               "${benchmark quick (toString script) []}" < "${f}" > "$out"
             '');

env = { buildInputs = [ (haskellPackages.ghcWithPackages (h: [ reduce-equations ])) ]; };

go = quick: clusterCount: clusters:
           map (doReduce quick clusterCount) clusters;

reduce = { quick, explored }:
  let results = mapAttrs (go quick) explored;
      failed  = any (n: any (x: x.failed) results."${n}") (attrNames results);
      result  = { inherit results failed; };
   in result;

}
