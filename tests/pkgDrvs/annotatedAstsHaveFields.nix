defs: with defs; pkg:
with builtins;

let checkField = f: drvFromScript { inherit (pkg) annotated; } ''
      set -e
      R=$(jq 'map(has("${f}")) | all' < "$annotated")

      if [[ "x$R" = "xtrue" ]]
      then
        touch "$out"
        exit 0
      fi

      echo "Got '$R' from '$annotated'" 1>&2
      exit 1
    '';

    fields = [ "package" "module" "name" "ast" "type" "arity" "quickspecable"
               "hashable" ];

 in listToAttrs (map (f: { name = f; value = checkField f; }) fields)
