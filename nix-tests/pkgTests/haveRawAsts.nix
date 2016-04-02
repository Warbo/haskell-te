defs: with defs; pkgName:

let asts           = dumpedPackages."${pkgName}";
    astsNonempty   = assertMsg (readFile "${asts}" != "")
                               "Checking '${asts}' is non-empty";
    count          = runScript { buildInputs = [ jq ]; } ''
                       jq -r 'length' < "${asts}" > "$out"
                     '';
    jCount         = addErrorContext "Parsing: '${count}'" (fromJSON count);
    jCountNonempty = assertMsg (jCount > 0) "Found no ASTs in '${asts}'";
 in astsNonempty && jCountNonempty
