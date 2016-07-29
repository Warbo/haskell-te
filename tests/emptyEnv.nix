defs: with defs; with lib;

# The contents of extra-haskell-packages should be available, even with no
# ENVIRONMENT_PACKAGES given
let

f = writeScript "dummy-json" "[]";

in drvFromScript {
     buildInputs = explore.extractedEnv null f;
     msg = "Default env contains extra-haskell-packages";
   }
   ''
     set -e
     while read -r PKG
     do
       unset ENVIRONMENT_PACKAGES
       "${explore.build-env}" ghc-pkg list "$PKG" || {
         echo "Extra package '$PKG' wasn't found with empty environment" 1>&2
         echo "not ok - $msg"
         exit 2
       }
     done < <(echo "${concatStringsSep "\n" explore.extra-haskell-packages}")
     echo "ok - $msg"
     echo "# $msg" >> "$out"
     echo "# true" >> "$out"
   ''
