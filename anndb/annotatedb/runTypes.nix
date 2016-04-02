{ runScript, adb-scripts, jq, withNix }:
asts: pkgName:

runScript (withNix { inherit asts pkgName; buildInputs = [ adb-scripts jq ]; })
          ''
            set -e
            runTypes "$pkgName" < "$asts" > typed.json

            RESULT=$(nix-store --add typed.json)
            printf '%s' "$RESULT" > "$out"
          ''
