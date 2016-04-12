defs: with defs; pkg:
with builtins;

let count = parseJSON (runScript { buildInputs = [ ML4HSFE ]; } ''
      set -e
      grep -c "^" < "${pkg.features}" > "$out" || true
    '');
 in fromJSON count > 0
