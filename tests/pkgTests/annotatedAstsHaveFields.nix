defs: with defs; pkg:

let checkField = f: parseJSON (runScript {} ''
      "${jq}/bin/jq" 'map(has("${f}")) | all' < "${pkg.preAnnotated}" > "$out"
    '');

    fields = [ "package" "module" "name" "ast" "type" "arity" "quickspecable" ];

    results = listToAttrs (map (f: { name = f; value = checkField f; }) fields);

 in all (f: assertMsg results."${f}"
                      "PreAnnotated ASTs for '${pkg.name}' have field '${f}'")
        fields