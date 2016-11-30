defs: with defs; pkg:
with builtins;

let count = drvFromScript { inherit (pkg) annotated; } ''
      set -e
      if jq -cr '.[] | .name' < "$annotated" |
           grep -cF ".$"
      then
        echo "Found core names in '$annotated'" 1>&2
        exit 1
      fi

      touch "$out"
      exit 0
    '';
 in {
      haveAnnotated = testMsg (pkg ? annotated) "Have annotated";

      annotatedExists = drvFromScript { inherit (pkg) annotated; } ''
                             if [[ -e "$annotated" ]]
                             then
                               touch "$out"
                               exit 0
                             fi

                             echo "annotated '$annotated'" doesn't exist" 1>&2
                             exit 1
                           '';

      noCoreNames = count;
    }
