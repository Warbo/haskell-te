defs: with defs; pkg:
with lib;

let check = c: data: parseJSON (runScript { buildInputs = [ jq ]; } ''
      set -e
      LENGTH=$(jq -c 'length' < "${data}") || {
        echo "Can't read formatted cluster from '${data}' for '${pkg.name}'" 1>&2
        exit 2
      }
      echo "true" > "$out"
    '');
    checkAll = mapAttrs (c: v: all (check c) v) pkg.formatted;
 in all (c: checkAll."${toString c}") defaultClusters
