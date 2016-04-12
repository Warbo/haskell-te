defs: with defs; pkg:
with builtins;
with lib;

let

check = data:
  let result = parseJSON (runScript { buildInputs = [ jq ]; } ''
        set -e
        jq 'map(.quickspecable) | all' < "${data}" > "$out"
      '');
   in testMsg result "Ensuring all quickspecable ${toJSON data}";

checkAll = mapAttrs (_: all check) pkg.formatted;

in all (c: checkAll.${toString c}) defaultClusters
