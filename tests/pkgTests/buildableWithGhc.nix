defs: with defs; pkg:
with builtins;

testRun "Trying to build" null { inherit (pkg.build) time; } ''
  O=$(jq -r '.mean.estPoint | type' < "$time")
  [[ "x$O" = "xstring" ]] && exit 0
  [[ "x$O" = "xnumber" ]] && exit 0
  exit 1
''
