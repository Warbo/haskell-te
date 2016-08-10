defs: with defs; pkg:
with builtins;

let asts      = pkg.annotated;
    haveField = field:
                  assert isString field;
                  testRun "Have ${field}" null { inherit asts; } ''
                    set -e
                    R=$(jq -rc 'map(has("${field}")) | all' < "$asts")
                    [[ "x$R" = "xtrue" ]] || exit 1
                    exit 0
                  '';
 in listToAttrs (map (n: { name = n; value = haveField n; })
                     [ "package" "module" "name" "ast" "type" "arity"
                       "quickspecable" "dependencies" ])
