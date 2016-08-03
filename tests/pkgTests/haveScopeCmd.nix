defs: with defs; pkg:
with builtins;

let result = parseJSON (readFile pkg.ranTypes);
 in {
  haveScopeCmd = testMsg (result ? scopecmd)
                         "${pkg.name} has scope command";
  nonEmpty     = testMsg (strip result.scopecmd != "")
                         "${pkg.name} scope command isn't empty";
}
