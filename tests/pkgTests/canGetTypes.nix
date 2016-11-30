defs: with defs; pkg:
with builtins;

let count = fromJSON (parseJSON (runScript {} ));
 in testRun "Found types for '${pkg.name}'" null { buildInputs = [ jq ]; } ''
      jq -re 'map(has("type") and .type != null) | any' < "${pkg.annotated}" > "$out"
    ''
