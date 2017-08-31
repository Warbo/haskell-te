defs: with defs; pkg:
with builtins;

with rec {
  inherit (pkg) asts;

  haveField = field:
    assert isString field;
    testRun "Have ${field}" null { inherit asts; } ''
      set -e
      R=$(jq -rc 'map(has("${field}")) | all' < "$asts")
      [[ "x$R" = "xtrue" ]] || exit 1
      exit 0
    '';
};

listToAttrs (map (n: { name = n; value = haveField n; })
                     [ "package" "module" "name" "ast" "type" "arity"
                       "quickspecable" "dependencies" ])
