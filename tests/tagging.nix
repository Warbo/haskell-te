defs: with defs;
with builtins;

testRun "Got array" null { buildInputs = [ GetDeps ]; } ''
  INPUT1='[{"name": "n1", "module": "M1"}, {"name": "n2", "module": "M2"}]'
  INPUT2='[{"name": "n2", "module": "M2", "foo": "bar"}]'
  RESULT=$(echo "$INPUT1" | "${tagAstsScript}" <(echo "$INPUT2") "{}")

  T=$(echo "$RESULT" | jq -r 'type')
  [[ "x$T" = "xarray" ]] && exit 0

  echo -e "INPUT1: $INPUT1\nINPUT2: $INPUT2\nRESULT: $RESULT\nT: $T" 1>&2
  exit 1
''
