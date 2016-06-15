{ getAritiesScript, getTypesScript, jq, tagAstsScript, writeScript }:

writeScript "annotateAsts" ''
  #!/usr/bin/env bash

  set -e

  function msg {
    echo -e "$1"
  }

  function tagTypes {
    NOTYPE='{"type":null}'
    "${tagAstsScript}" <(echo "$RAWSCOPE" | "${getTypesScript}") "$NOTYPE"
  }

  function tagArities {
    NOARITY='{"arity":null,"quickspecable":false}'
    "${tagAstsScript}" <(echo "$RAWTYPES" | "${getAritiesScript}") "$NOARITY"
  }

     INPUT=$(cat)
   RAWASTS=$(echo "$INPUT" | "${jq}/bin/jq" -c '.asts')
  RAWTYPES=$(echo "$INPUT" | "${jq}/bin/jq" -r '.result')
  RAWSCOPE=$(echo "$INPUT" | "${jq}/bin/jq" -r '.scoperesult')

  echo "$RAWASTS" | tagTypes | tagArities
''
