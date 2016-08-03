defs: with defs; pkg:
with builtins;

let count = fromJSON (parseJSON (runScript {} ''
      "${jq}/bin/jq" -r 'length' < "${pkg.gotTypes}" > "$out"
    ''));
 in testDbg (count > 0) "Found types for '${pkg.name}'"
    {
      inherit count;
      inherit (pkg) gotTypes;
    }
