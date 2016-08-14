defs: with defs;
with builtins;

let

clusterScript = writeScript "cluster-script" ''
  ml4hsfe-loop | "${recurrentClusteringScript}"
'';

ex = ./ml4hsfeExamples/ml4hsfe-outer-loop-example-input.json;

env = { buildInputs = [ haskellPackages.ML4HSFE ]; };

vars = ''
  export WIDTH=30
  export HEIGHT=30
  export CLUSTERS=4
'';

shOutput = drvFromScript env ''
  ${vars}
  "${clusterScript}" < "${ex}" > "$out"
'';

progOutput = drvFromScript env ''
  ${vars}
  ml4hsfe-outer-loop < "${ex}" > "$out"
'';

in drvFromScript (env // { inherit shOutput progOutput; }) ''
  set -e
  for EXPR in type length 'map(type)' 'map(has("cluster"))'
  do
      SH=$(jq "$EXPR" <   "$shOutput")
    PROG=$(jq "$EXPR" < "$progOutput")

    [[ "x$SH" = "x$PROG" ]] || {
      echo "Mismatch for '$EXPR': '$SH' vs '$PROG'" 1>&2
      exit 2
    }
  done

  touch "$out"
''
