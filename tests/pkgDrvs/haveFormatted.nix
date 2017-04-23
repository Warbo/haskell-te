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
      jq -e -r "$1" < "$formatted" && return 0

      echo "jqMatch for '$1' failed" 1>&2

      cat "$formatted" 1>&2
      exit 1
    }

    jqMatch     'type | . == "array"'
    jqMatch 'map(type | . == "object") | all'

    exit 0
  '';
in mapAttrs doTest pkg.formatted
