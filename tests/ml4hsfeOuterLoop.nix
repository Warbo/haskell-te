defs: with defs;
with builtins;

let

clusterScript = writeScript "cluster-script" ''
  ml4hsfe-loop | "${recurrentClusteringScript}"
'';

ex = let f = ./ml4hsfeExamples/ml4hsfe-outer-loop-example-input.json;
      in drvFromScript {} ''
           # Select 50 random ASTs
           ASTS=$(jq -c '.[]' < "${f}")
           echo "$ASTS" | shuf | head -n50 | jq -s '.' > "$out"
         '';

env = { EXAMPLE = ex; buildInputs = [ haskellPackages.ML4HSFE runWeka ]; };

vars = ''
  export WIDTH=30
  export HEIGHT=30
  export CLUSTERS=4
'';

shOutput = writeScript "sh" ''
  ${vars}
  "${clusterScript}" < "$EXAMPLE"
'';

progOutput = writeScript "prog" ''
  ${vars}
  ml4hsfe-outer-loop < "$EXAMPLE"
'';

in trace "FIXME: Is Haskell or Shell more correct?" drvFromScript (env // { inherit shOutput progOutput; }) ''
  set -e
  echo "Running shell version" 1>&2
    SH=$("$shOutput")

  echo "Running Haskell version" 1>&2
  PROG=$("$progOutput")

  for EXPR in type length 'map(type)' 'map(has("cluster"))'
  do
      GOTSH=$(echo "$SH"   | jq "$EXPR")
    GOTPROG=$(echo "$PROG" | jq "$EXPR")

    [[ "x$GOTSH" = "x$GOTPROG" ]] && continue

    echo "Mismatch for '$EXPR'" 1>&2
    echo "Shell version:"       1>&2
    echo "$GOTSH"               1>&2
    echo "Haskell version:"     1>&2
    echo "$GOTPROG"             1>&2
  done

  touch "$out"
''
