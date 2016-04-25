{ benchmark, dump-package, parseJSON, runScript }:
{ quick, pkgDir }:

assert builtins.pathExists pkgDir;

parseJSON (runScript { buildInputs = [ ]; } ''
  set -e
  cp -r "${pkgDir}" ./pkgDir
  chmod +w -R pkgDir

  echo "Dumping '${pkgDir}'" 1>&2
  HOME="$USER_HOME" DIR="$PWD/pkgDir" \
    "${benchmark quick dump-package []}" > "$out"
'')
