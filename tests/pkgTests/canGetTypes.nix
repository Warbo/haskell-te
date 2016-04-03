defs: with defs; pkg:

let count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${pkg.gotTypes}" > "$out"
    ''));
 in assertMsg (count > 0) "Found '${count}' types for '${pkg.name}'"
