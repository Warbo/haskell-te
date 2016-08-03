defs: with defs; pkg:
with builtins;

let result = parseJSON (readFile pkg.ranTypes);
 in {
 haveResult = testMsg (result ? result)
                      "${pkg.name} has ranTypes.result";
 nonEmpty   = testMsg (strip result.result != "")
                      "${pkg.name} ranTypes.result isn't empty";
}
