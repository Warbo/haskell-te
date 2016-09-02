defs: with defs; with lib;

mapAttrs (name: testRun name null { buildInputs = [ package ]; }) {
  canRun = ''
    mlspecBench < ${./example.smt2} || exit 1
  '';

  outputIsJson = ''
    OUTPUT=$(mlspecBench < ${./example.smt2}) || exit 1
    TYPE=$(echo "$OUTPUT" | jq -r 'type') || {
      echo -e "START OUTPUT\n$OUTPUT\nEND OUTPUT" 1>&2
      exit 1
    }
    [[ "x$TYPE" = "xobject" ]] || {
      echo -e "START OUTPUT\n$OUTPUT\nEND OUTPUT" 1>&2
      echo "Type is '$TYPE' instead of object" 1>&2
      exit 1
    }
  '';

  haveEquations = ''
    OUTPUT=$(mlspecBench < ${./example.smt2})   || exit 1
     CHECK=$(echo "$OUTPUT" | jq 'has("result")') || exit 1
    [[ "x$CHECK" = "xtrue" ]] || {
      echo -e "Didn't find 'result' in\n$OUTPUT" 1>&2
      exit 1
    }
  '';
}
