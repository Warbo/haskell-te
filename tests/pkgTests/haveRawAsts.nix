defs: with defs;

pkgName:

let asts    = downloadAndDump pkgName;
    counter = writeScript "counter" ''
        jq -r 'length' < "${asts}"
      '';
    count   = runCommand "count" { buildInputs = [ jq asts ]; } counter;
 in fromJSON (readFile "${count}") == true
