defs: with defs; pkg:

let annotated = testAnnotated."${pkg.name}";

    count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${annotated}" > "$out"
    ''));
 in assertMsg (count > 0) "Found '${count}' annotated ASTs for '${pkg.name}'"
