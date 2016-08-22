{ benchmark, drvFromScript, dump-package, explore, writeScript }:
{ quick, pkgDir }:

drvFromScript {
    inherit pkgDir;
    buildInputs = explore.extractedEnv {};
  } ''
  set -e

  [[ -d "$pkgDir" ]] || {
    echo "Couldn't find directory to dump '$pkgDir'" 1>&2
    exit 1
  }

  cp -r "$pkgDir" ./pkgDir
  chmod +w -R pkgDir

  echo "Dumping '$pkgDir'" 1>&2
  HOME="$PWD" DIR="$PWD/pkgDir" \
    "${benchmark {
         inherit quick;
         cmd = dump-package;
     }}" > "$out"
''
