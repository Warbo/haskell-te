{ fail, jq, lib, runCommand, withNix, wrap, writeScript }:
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

  fromStdin = wrap {
    name   = "format-stdin";
    paths  = [ fail jq ];
    vars   = {
      FILTER =
        "map(select(.cluster == $cl and .type != null and .quickspecable))";
    };
    script = ''
      set -e
      set -o pipefail
      [[ -n "$clCount" ]] || fail "No clCount given, aborting"

      INPUT=$(cat)

      # Select entries which have a "cluster" attribute matching the given
      # number, a non-null "type" attribute and a true "quickspecable" attribute
      function clusterContent {
        echo "$INPUT" | jq -c --argjson cl "$1" "$FILTER | map(del(.features))"
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
        # Work out the relevant output path; we use "$out1" "$out2", etc. to
        # avoid clashing with bash's argument names "$1", "$2", etc.
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
  };

  format = clusterCount: clusters:
    let cCount = fromJSON clusterCount;
        result = runCommand "format" (withNix {
                                       inherit clusters;
                                       clCount = toString clusterCount;
                                       outputs = map (n: "out" + toString n)
                                                     (range 1 cCount); })
                                     script;

        wrapped = map (n: result."out${toString n}") (range 1 cCount);
     in assert isList wrapped;
        assert isString clusterCount;
        assert isInt cCount;
        wrapped;
}
