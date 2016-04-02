defs: with defs; pkgName:

let result = asts:
      let str = runScript { buildInputs = [ jq ]; } ''
            RESULTS="{}"
            for FIELD in package module name ast
            do
              # RESULTS accumulates whether all ASTs have each field, and that
              # they're non-empty
              RESULTS=$(jq -n --argfile asts    "${asts}"          \
                              --argfile results <(echo "$RESULTS") \
                              --arg     field   "$FIELD"           \
                '$results + {($field) : ($asts                             |
                                         map(has($field) and
                                             (.[$field] | length | . > 0)) |
                                         all)}')
            done
            echo "$RESULTS" > "$out"
          '';
          json = parseJSON str;
       in assert isString asts;
          assert isString str;
          assert isAttrs  json;
          json;
    check = asts: all id (mapAttrsToList (f: b: assertMsg b "Checking for ${f}")
                                         (result asts));
 in all check [ quickDumps."${pkgName}" slowDumps."${pkgName}" ]
