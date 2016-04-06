defs: with defs; pkg:

let count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${pkg.preAnnotated}" > "$out"
    ''));
 in testMsg (count > 0)
            "Found '${toString count}' pre-annotated ASTs for '${pkg.name}'"
