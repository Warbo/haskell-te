defs: with defs; pkg:

let rawData = runTypes pkg.dump pkg.name;

    annotated = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      annotateAsts < "${rawData}" > annotated.json
      "${storeResult}" annotated.json "$out"
    '';

    checkField = f: parseJSON (runScript {} ''
      "${jq}/bin/jq" 'map(has("${f}")) | all' < "${annotated}" > "$out"
    '');

    fields = [ "package" "module" "name" "ast" "type" "arity" "quickspecable" ];

    results = listToAttrs (map (f: { name = f; value = checkField f; }) fields);

 in all (f: assertMsg results."${f}"
                      "Annotated ASTs for '${pkg.name}' have field '${f}'")
        fields
