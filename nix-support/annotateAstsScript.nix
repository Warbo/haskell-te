{ writeScript }:

builtins.trace "FIXME: Port tagAsts, getTypes, getArities" writeScript "annotateAsts" ''
  #!/usr/bin/env bash

  set -e

  function msg {
    echo -e "$1"
  }

  command -v jq > /dev/null || {
    msg "ERROR: annotateAsts requires jq"
    exit 1
  }

  BASE=$(dirname "$0")

  function tagTypes {
    NOTYPE='{"type":null}'
    "$BASE/tagAsts" <(echo "$RAWSCOPE" | "$BASE/getTypes") "$NOTYPE"
  }

  function tagArities {
    NOARITY='{"arity":null,"quickspecable":false}'
    "$BASE/tagAsts" <(echo "$RAWTYPES" | "$BASE/getArities") "$NOARITY"
  }

     INPUT=$(cat)
   RAWASTS=$(echo "$INPUT" | jq -c '.asts')
  RAWTYPES=$(echo "$INPUT" | jq -r '.result')
  RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult')

  echo "$RAWASTS" | tagTypes | tagArities
''
