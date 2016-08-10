defs: with defs; pkg:
with builtins;

let asts      = pkg.annotated;
    haveField = field:
                  assert isString field;
                  assert pathExists "${asts}";
                  runScript { buildInputs = [ jq ]; } ''
                    set -e
                    jq -c 'map(has("${field}")) | all' < "${asts}" > "$out"
                  '';
    checkField = field:
                   let result     = haveField field;
                       jResult    = addErrorContext "Parsing JSON '${result}'"
                                                    (fromJSON result);
                       safeResult = if result == ""
                                       then trace "Empty result for '${field}'"
                                                  false
                                       else jResult;
                    in testMsg safeResult "Checking JSON has field '${field}'";
 in testWrap (map checkField [
      "package"
      "module"
      "name"
      "ast"
      "type"
      "arity"
      "quickspecable"
      "dependencies"
    ]) "Have fields for package '${pkg.name}'"
