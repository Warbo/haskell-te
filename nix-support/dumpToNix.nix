{ benchmark, c2db-scripts, parseJSON, runScript, withNix }:
{ quick, pkgDir }:

assert builtins.pathExists pkgDir;

parseJSON (runScript (withNix { buildInputs = [ c2db-scripts ]; }) ''
  set -e
  cp -r "${pkgDir}" ./pkgDir
  chmod +w -R pkgDir

  echo "Dumping '${pkgDir}'" 1>&2
  HOME="$USER_HOME" DIR="$PWD/pkgDir" \
    "${benchmark quick "dump-package" []}" > "$out"
'')
