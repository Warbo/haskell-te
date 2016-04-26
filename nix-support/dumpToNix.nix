{ benchmark, dump-package, parseJSON, runScript }:
{ quick, pkgDir }:

let dir = builtins.unsafeDiscardStringContext "${toString pkgDir}";
 in parseJSON (runScript { buildInputs = [ ]; } ''
      set -e

      D="${toString pkgDir}"

      [[ -d "$D" ]] || {
        echo "Couldn't find directory to dump '$D'" 1>&2
        exit 1
      }

      cp -r "$D" ./pkgDir
      chmod +w -R pkgDir

      echo "Dumping '$D'" 1>&2
      HOME="$USER_HOME" DIR="$PWD/pkgDir" \
        "${benchmark quick dump-package []}" > "$out"
    '')
