{ drvFromScript, ensureVars, lib, writeScript }:
with builtins;
with lib;

rec {
  script = ''
    [[ -f "$clusters" ]] || {
      echo "Given cluster file '$clusters' doesn't exist" 1>&2
      exit 2
    }
    "${fromStdin}" < "$clusters"
  '';

  fromStdin = writeScript "format-stdin" ''
    set -e

    INPUT=$(cat)

    # Select entries which have a "cluster" attribute matching the given number,
    # a non-null "type" attribute and a true "quickspecable" attribute.
    FILTER='map(select(.cluster == $cls and .type != null and .quickspecable))'
    function clusterContent {
      echo "$INPUT" | jq -c --argjson cls "$1" "$FILTER | map(del(.features))"
    }

    function postProcess {
      if [[ -n "$SIMPLE" ]]
      then
        jq -s '.'
      else
        cat
      fi
    }

    for CLUSTER in $(seq 1 "$clCount")
    do
      # Work out the relevant output path; we use "$out1" "$out2", etc. to avoid
      # clashing with bash's argument names "$1", "$2", etc.
      if [[ -n "$SIMPLE" ]]
      then
        clusterContent "$CLUSTER"
      else
        outPath=$(eval echo "\$out$CLUSTER")

        # Store the cluster's content at this path
        clusterContent "$CLUSTER" > "$outPath"
      fi
    done | postProcess
  '';

  format = clusterCount: clusters:
    let cCount = fromJSON clusterCount;
        result = drvFromScript { inherit clusters;
                                 clCount = toString clusterCount;
                                 outputs = map (n: "out" + toString n)
                                               (range 1 cCount); }
                               script;

        wrapped = map (n: result."out${toString n}") (range 1 cCount);
     in assert isList wrapped;
        assert isString clusterCount;
        assert isInt cCount;
        wrapped;
}
