{ benchmark, haskellPackages, lib, parseJSON, reduce-equations, runScript, writeScript }:
with builtins;
with lib;

rec {

script = writeScript "reduce-equations" "reduce-equations";

mkCat = inputs: "cat " + concatStringsSep " " (map (x: ''"${x}"'') inputs);

doReduce = quick: clusterCount: inputs:
             parseJSON (runScript env ''
               set -e
               export CLUSTERS="${clusterCount}"
               ${mkCat inputs} | "${benchmark quick (toString script) []}" > "$out"
             '');

env = { buildInputs = [ (haskellPackages.ghcWithPackages (h: [ reduce-equations ])) ]; };

reduce = { quick, explored }:
  let results = mapAttrs (doReduce quick) explored;
      failed  = any (n: any (x: x.failed) results."${n}") (attrNames results);
      result  = { inherit results failed; };
   in result;

}
