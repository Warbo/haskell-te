{ benchmark, dump-package, parseJSON, runScript }:
{ quick, pkgDir }:

let dir    = builtins.unsafeDiscardStringContext "${toString pkgDir}";
    script = ''
      D="${toString pkgDir}"

      [[ -d "$D" ]] || {
        echo "Couldn't find directory to dump '$D'" 1>&2
        exit 1
      }

      cp -r "$D" ./pkgDir
      chmod +w -R pkgDir

      echo "Dumping '$D'" 1>&2
      HOME="$PWD" DIR="$PWD/pkgDir" "${dump-package}"
    '';
 in benchmark quick script [] null
