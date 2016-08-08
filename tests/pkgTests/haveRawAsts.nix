defs: with defs; pkg:
with builtins;

let asts           = pkg.rawDump.stdout;
    astsNonempty   = testDbg (readFile "${asts}" != "")
                             "Checking asts is non-empty"
                             { inherit asts; inherit (pkg) rawDump build; };
    count          = runScript {} ''
                       jq -r 'length' < "${asts}" > "$out"
                     '';
    jCount         = addErrorContext "Parsing: '${count}'" (fromJSON count);
    result         = if count == ""
                        then trace "Got empty count" false
                        else jCount > 0;
    jCountNonempty = testDbg result "Found ASTs in '${asts}'"
                       { inherit result jCount count asts; };
 in testWrap [ astsNonempty jCountNonempty ] "Have raw ASTs for ${pkg.name}"
