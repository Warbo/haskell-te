defs: with defs; pkgName:

let asts   = dumpedPackages."${pkgName}";
    result = runScript { buildInputs = [ jq ]; } ''
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
    fields     = fromJSON result;
    fieldFound = f: fields."${f}";
 in all fieldFound (attrNames fields)
