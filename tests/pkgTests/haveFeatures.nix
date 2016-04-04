defs: with defs; pkg:

let count = parseJSON (runScript { buildInputs = [ ML4HSFE ]; } ''
      set -e
      grep -c "^" < "${pkg.features}" > "$out" || true
    '');
 in fromJSON count > 0
