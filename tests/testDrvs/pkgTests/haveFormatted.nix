defs: with defs; pkg:
with builtins;
with lib;

let toAttrs = l: n: if l == []
                       then {}
                       else { "${toString n}" = head l; } //
                            toAttrs (tail l) (n+1);

    doTest = cCount: cs: mapAttrs (go cCount) (toAttrs cs 1);

    go = cCount: c: f: testRun
           "Have formatted ASTs for ${c}/${cCount} cluster of ${pkg.name}"
           null
           { formatted = f; }
           ''
    function jqMatch {
      RESULT=$(jq -r "$1" < "$formatted")
      [[ "x$RESULT" = "x$2" ]] && return 0

      echo "jqMatch for '$1' found '$RESULT', not '$2'" 1>&2

      cat "$formatted" 1>&2
      exit 1
    }

    echo "Checking we got an array" 1>&2
    jqMatch 'type | . == "array"' 'true'

    echo "Checking lists contain objects" 1>&2
    jqMatch 'map(type | . == "object") | all' 'true'

    echo "Checking objects contain features" 1>&2
    jqMatch 'map(.features | type | . == "array") | all' 'true'

    exit 0
  '';
in mapAttrs doTest pkg.formatted
