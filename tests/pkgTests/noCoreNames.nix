defs: with defs; pkg:
with builtins;

let count = parseJSON (runScript {} ''
      set -e
      "${jq}/bin/jq" -cr '.[] | .name' < "${pkg.preAnnotated}" |
        grep -cF ".$" > "$out" || true # Grep "fails" when we succeed
    '');
 in testMsg (pkg ? preAnnotated) "Have preAnnotated"                  &&
    testMsg (pathExists pkg.preAnnotated)
            "'${pkg.name}.preAnnotated' (${pkg.preAnnotated}) exists" &&
    testMsg (count == "0")
            "Found '${count}' Core names beginning with $ for '${pkg.name}'"
