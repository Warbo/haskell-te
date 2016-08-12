defs: with defs; pkg:
with builtins;

let checkField = f: drvFromScript { inherit (pkg) preAnnotated; } ''
      set -e
      R=$(jq 'map(has("${f}")) | all' < "$preAnnotated")

      if [[ "x$R" = "xtrue" ]]
      then
        touch "$out"
        exit 0
      fi

      echo "Got '$R' from '$preAnnotated'" 1>&2
      exit 1
    '';

    fields = [ "package" "module" "name" "ast" "type" "arity" "quickspecable" ];

 in listToAttrs (map (f: { name = f; value = checkField f; }) fields)
