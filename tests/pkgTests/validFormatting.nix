defs: with defs; pkg:
with lib;

let check = c: data: parseJSON (runScript { buildInputs = [ jq ]; } ''
      set -e
      LENGTH=$(jq -c 'length' < "${data}") || {
        echo "Can't read '${c}' formatted clusters for '${pkg.name}'" 1>&2
        exit 2
      }
      [[ "$LENGTH" -eq "${c}" ]] || [[ "$LENGTH" -lt "${c}" ]] || {
        echo "Formatted '$LENGTH' clusters for '${pkg.name}' instead of '${c}'" 1>&2
        exit 3
      }
      echo "true" > "$out"
    '');
    checkAll = mapAttrs check pkg.formatted;
 in all (c: checkAll."${toString c}") defaultClusters
