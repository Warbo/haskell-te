defs: with defs; pkgName:

let asts    = downloadAndDump pkgName;
    count   = runScript { buildInputs = [ jq ]; } ''
                jq -r 'length' < "${asts}" > "$out"
              '';
 in fromJSON count > 0
