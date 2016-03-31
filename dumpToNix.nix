{ runScript, c2db-scripts, withNix }:
pkgDir:

assert builtins.pathExists pkgDir;

runScript (withNix { inherit pkgDir; buildInputs = [ c2db-scripts ]; })
  ''
    cp -r "$pkgDir" ./pkgDir || exit 1
    chmod +w -R pkgDir       || exit 1

    HOME="$USER_HOME" dump-package "$PWD/pkgDir" > dump.json || exit 1

    RESULT=$(nix-store --add dump.json) || exit 1
    printf '%s' "$RESULT" > "$out"
  ''
