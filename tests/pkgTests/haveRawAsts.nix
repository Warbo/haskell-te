defs: with defs; pkg:

let doCheck = asts:
  let astsNonempty   = testMsg (readFile "${asts}" != "")
                               "Checking '${asts}' is non-empty";
      count          = runScript { buildInputs = [ jq ]; } ''
                         jq -r 'length' < "${asts}" > "$out"
                       '';
      jCount         = addErrorContext "Parsing: '${count}'" (fromJSON count);
      jCountNonempty = testMsg (jCount > 0) "Found no ASTs in '${asts}'";
   in astsNonempty && jCountNonempty;
 in doCheck pkg.rawDump.stdout
