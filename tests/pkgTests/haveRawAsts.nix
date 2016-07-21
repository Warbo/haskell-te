defs: with defs; pkg:
with builtins;

let asts    = pkg.rawDump.stdout;
    astsNonempty   = testMsg (readFile "${asts}" != "")
                             "Checking '${asts}' is non-empty";
    count          = runScript { buildInputs = [ jq ]; } ''
                       jq -r 'length' < "${asts}" > "$out"
                     '';
    jCount         = addErrorContext "Parsing: '${count}'" (fromJSON count);
    result         = if count == ""
                        then trace "Got empty count" false
                        else jCount > 0;
    jCountNonempty = testMsg result "Found no ASTs in '${asts}'";
 in testWrap [ astsNonempty jCountNonempty ] "Have raw ASTs for ${pkg.name}"
