defs: with defs; pkg:

let count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${pkg.preAnnotated}" > "$out"
    ''));
 in assertMsg (count > 0)
              "Found '${count}' pre-annotated ASTs for '${pkg.name}'"
