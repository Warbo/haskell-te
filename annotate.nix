{ runScript, adb-scripts, jq, withNix }:
asts: pkgName:

runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
    set -e
    annotateDb "${pkgName}" < "${asts}" > annotated.json
    RESULT=$(nix-store --add annotated.json)
    printf '%s' "$RESULT" > "$out"
  ''
