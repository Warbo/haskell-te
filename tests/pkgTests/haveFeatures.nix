defs: with defs; pkg:

let count = parseJSON (runScript { buildInputs = [ ML4HSFE ]; } ''
      set -e
      WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${pkg.annotated}" |
        grep -c "^" > "$out" || true
    '');
 in fromJSON count > 0
