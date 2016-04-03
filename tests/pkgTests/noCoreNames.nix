defs: with defs; pkg:

let count = parseJSON (runScript {} ''
      set -e
      "${jq}/bin/jq" -cr '.[] | .name' < "${pkg.annotated}" |
        grep -cF ".$" > "$out" || true # Grep "fails" when we succeed
    '');
 in assertMsg (pkg ? annotated) "Have annotated"                  &&
    assertMsg (pathExists pkg.annotated)
              "'${pkg.name}.annotated' (${pkg.annotated}) exists" &&
    assertMsg (count == "0")
              "Found '${count}' Core names beginning with $ for '${pkg.name}'"
