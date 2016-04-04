defs: with defs; pkg:
with lib;

let check = c: data: parseJSON (runScript { buildInputs = [ jq ]; } ''
      set -e
      jq 'map(.[] | .quickspecable) | all' < "${data}" > "$out"
    '');
    checkAll = mapAttrs check pkg.formatted;
 in all (c: checkAll."${toString c}") defaultClusters
