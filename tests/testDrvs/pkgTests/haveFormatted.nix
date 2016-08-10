defs: with defs; pkg:
with builtins;
with lib;

testRun "Have formatted ASTs for ${pkg.name}" null { inherit (pkg) formatted; }
  ''
    function jqMatch {
      RESULT=$(jq -r "$1" < "$formatted")
      [[ "x$RESULT" = "x$2" ]] && return 0

      echo "jqMatch for '$1' found '$RESULT', not '$2'" 1>&2
      exit 1
    }

    echo "Checking we got a set" 1>&2
    jqMatch 'type' 'object'

    echo "Checking keys are numeric" 1>&2
    jqMatch 'keys | map(. as $this | try tonumber catch $this | type | . == "number") | all' 'true'

    echo "Checking values are lists" 1>&2
    jqMatch '[.[]] | map(type | . == "array") | all' 'true'

    echo "Checking lists contain strings" 1>&2
    jqMatch '[.[]] | add | map(type | . == "string") | all' 'true'

    exit 0
  ''
