defs: with defs;

let check  = name: result: parseJSON (runScript {} ''
      set -e
      "${jq}/bin/jq" '.' < "${result}" > /dev/null
      echo true > "$out"
    '');
    checks = mapAttrs check totalTimes;
 in all (pkg: checks."${pkg}") testPackageNames
