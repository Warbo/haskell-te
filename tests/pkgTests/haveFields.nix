defs: with defs;

pkgName:

assert isString pkgName;
let asts      = annotatedPackages."${pkgName}";
    haveField = field:
                  assert isString field;
                  assert pathExists "${asts}";
                  runScript { buildInputs = [ jq ]; } ''
                    set -e
                    jq -c 'map(has("${field}")) | all' < "${asts}" > "$out"
                  '';
    checkField = field:
                   let result  = haveField field;
                       jResult = addErrorContext "Parsing '${result}' as JSON"
                                                 (fromJSON result);
                    in assertMsg jResult "Checking JSON has field '${field}'";
 in all checkField [
      "package"
      "module"
      "name"
      "ast"
      "type"
      "arity"
      "quickspecable"
      "dependencies"
    ]
