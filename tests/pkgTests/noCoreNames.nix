defs: with defs; pkg:

let count = parseJSON (runScript {} ''
      set -e
      "${jq}/bin/jq" -cr '.[] | .name' < "${pkg.preAnnotated}" |
        grep -cF ".$" > "$out" || true # Grep "fails" when we succeed
    '');
 in assertMsg (pkg ? preAnnotated) "Have preAnnotated"                  &&
    assertMsg (pathExists pkg.preAnnotated)
              "'${pkg.name}.preAnnotated' (${pkg.preAnnotated}) exists" &&
    assertMsg (count == "0")
              "Found '${count}' Core names beginning with $ for '${pkg.name}'"
