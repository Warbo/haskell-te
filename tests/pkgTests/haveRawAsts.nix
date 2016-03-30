defs: with defs;

pkgName:

let asts    = downloadAndDump pkgName;
    counter = writeScript "counter" ''
        jq -r 'length' < "${asts}" > "$out"
      '';
    count   = runCommand "count" { buildInputs = [ jq ]; } counter;
 in fromJSON (readFile "${count}") > 0
