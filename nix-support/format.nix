{ drvFromScript, lib }:
with builtins;
with lib;

clusterCount: clusters:

let cCount = fromJSON clusterCount;
    result = drvFromScript { inherit clusters;
                             outputs = map (n: "out" + toString n)
                                           (range 1 cCount); } ''
  set -e

  [[ -f "$clusters" ]] || {
    echo "Given cluster file '$clusters' doesn't exist" 1>&2
    exit 2
  }

  # Select entries which have a "cluster" attribute matching the given number, a
  # non-null "type" attribute and a true "quickspecable" attribute.
  FILTER='map(select(.cluster == $cls and .type != null and .quickspecable))'
  function clusterContent {
    jq -c --argjson cls "$1" "$FILTER" < "$clusters"
  }

  for CLUSTER in $(seq 1 "${clusterCount}")
  do
    # Work out the relevant output path; we use "$out1" "$out2", etc. to avoid
    # clashing with bash's argument names "$1", "$2", etc.
    outPath=$(eval echo "\$out$CLUSTER")

    # Store the cluster's content at this path
    clusterContent "$CLUSTER" > "$outPath"
  done
'';

    wrapped = map (n: result."out${toString n}") (range 1 cCount);

in

assert isList wrapped;
assert isString clusterCount;
assert isInt cCount;
wrapped
