defs: with defs; pkg:
with builtins;

let count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${pkg.gotTypes}" > "$out"
    ''));
 in testMsg (count > 0) "Found '${toString count}' types for '${pkg.name}'"
