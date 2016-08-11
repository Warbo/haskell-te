defs: with defs; pkg:
with builtins;

let count = drvFromScript { inherit (pkg) preAnnotated; } ''
      set -e
      if jq -cr '.[] | .name' < "$preAnnotated" |
           grep -cF ".$"
      then
        echo "Found core names in '$preAnnotated'" 1>&2
        exit 1
      fi

      touch "$out"
      exit 0
    '';
 in {
      havePreannotated = testMsg (pkg ? preAnnotated) "Have preAnnotated";

      preannotatedExists = drvFromScript { inherit (pkg) preAnnotated; } ''
                             if [[ -e "$preAnnotated" ]]
                             then
                               touch "$out"
                               exit 0
                             fi

                             echo "preAnnotated '$preAnnotated'" doesn't exist" 1>&2
                             exit 1
                           '';

      noCoreNames = count;
    }
