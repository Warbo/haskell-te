{ jq, parseJSON, runScript, storeResult }:
with builtins;

clusterCount: clusters:

assert isString clusterCount;
assert isInt (fromJSON clusterCount);
assert isString "${clusters}";

let result = parseJSON (runScript { buildInputs = [ jq ]; } ''
  set -e

  [[ -f "${clusters}" ]] || {
    echo "Given cluster file '${clusters}' doesn't exist" 1>&2
    exit 2
  }

  # Select entries which have a "cluster" attribute matching the given number, a
  # non-null "type" attribute and a true "quickspecable" attribute.
  FILTER='map(select(.cluster == $cls and .type != null and .quickspecable))'
  function clusterContent {
    jq -c --argjson cls "$1" "$FILTER" < "${clusters}"
  }

  function clusterPaths {
    for CLUSTER in $(seq 1 "${clusterCount}")
    do
      # Store the cluster's content
      clusterContent "$CLUSTER" > cluster.json
      nix-store --add cluster.json
    done
  }

  # Read the paths into JSON strings then accumulate into an array
  clusterPaths | jq -R '.' | jq -s '.' > "$out"
'');

in

assert isList result;
result
