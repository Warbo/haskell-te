defs: with defs; pkg:
with builtins;

let asts           = pkg.rawDump.stdout;
    astsNonempty   = testRun "Checking asts is non-empty" null
                             { inherit asts; } ''
                               O=$(cat "$asts")
                               [[ -n "$O" ]] || exit 1
                             '';
    count          = drvFromScript { inherit asts; } ''
                       jq -r 'length' < "$asts" > "$out"
                     '';
    jCount         = addErrorContext "Parsing: '${count}'" (fromJSON (readFile count));
    result         = if count == ""
                        then trace "Got empty count" false
                        else jCount > 0;
    jCountNonempty = testDbg result "Found ASTs in '${asts}'"
                       { inherit result jCount count asts; };
 in testWrap [ astsNonempty jCountNonempty ] "Have raw ASTs for ${pkg.name}"
