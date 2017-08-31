defs: with defs; pkg:
with builtins;

let count = drvFromScript { inherit (pkg) asts; } ''
      set -e
      if jq -cr '.[] | .name' < "$asts" |
           grep -cF ".$"
      then
        echo "Found core names in '$asts'" 1>&2
        exit 1
      fi

      touch "$out"
      exit 0
    '';
 in {
      annotatedExists = drvFromScript { inherit (pkg) asts; } ''
                             if [[ -e "$asts" ]]
                             then
                               touch "$out"
                               exit 0
                             fi

                             echo "annotated '$asts'" doesn't exist" 1>&2
                             exit 1
                           '';

      noCoreNames = count;
    }
