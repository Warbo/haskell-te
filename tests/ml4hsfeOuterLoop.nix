defs: with defs;
with builtins;

let

clusterScript = writeScript "cluster-script" ''
  ml4hsfe-loop | "${recurrentClusteringScript}"
'';

wekaCli = import ../recurrent-clustering/weka-cli.nix;

ex = ./ml4hsfeExamples/ml4hsfe-outer-loop-example-input.json;

env = { buildInputs = [ wekaCli jq order-deps haskellPackages.ML4HSFE ]; };

vars = ''
  export WIDTH=30
  export HEIGHT=30
  export CLUSTERS=4
'';

shOutput = runScript env ''
  ${vars}
  "${clusterScript}" < "${ex}" > sh_output
  "${storeResult}" sh_output "$out"
'';

progOutput = runScript env ''
  ${vars}
  ml4hsfe-outer-loop < "${ex}" > prog_output
  "${storeResult}" prog_output "$out"
'';

test = runScript env ''
  set -e
  for EXPR in type length 'map(type)' 'map(has("cluster"))'
  do
      SH=$(jq "$EXPR" <   "${shOutput}")
    PROG=$(jq "$EXPR" < "${progOutput}")

    [[ "x$SH" = "x$PROG" ]] || {
      echo "Mismatch for '$EXPR': '$SH' vs '$PROG'" 1>&2
      exit 2
    }
  done

  echo "true" > "$out"
'';

in trace "FIXME: Skipping expensive ml4hsfeOuterLoop test" true
#testMsg (parseJSON test) "ml4hsfe-outer-loop behaves"
