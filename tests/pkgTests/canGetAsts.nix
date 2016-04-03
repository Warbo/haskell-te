defs: with defs; pkg:

let count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${pkg.annotated}" > "$out"
    ''));
 in assertMsg (count > 0) "Found '${count}' annotated ASTs for '${pkg.name}'"
