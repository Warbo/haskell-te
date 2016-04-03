defs: with defs; pkg:

let checkField = f: parseJSON (runScript {} ''
      "${jq}/bin/jq" 'map(has("${f}")) | all' < "${pkg.annotated}" > "$out"
    '');

    fields = [ "package" "module" "name" "ast" "type" "arity" "quickspecable" ];

    results = listToAttrs (map (f: { name = f; value = checkField f; }) fields);

 in all (f: assertMsg results."${f}"
                      "Annotated ASTs for '${pkg.name}' have field '${f}'")
        fields
