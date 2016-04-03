{ adb-scripts, jq, runScript, storeResult, withNix }:
asts: pkgName:

runScript (withNix { buildInputs = [ adb-scripts jq ]; })
          ''
            set -e
            runTypes "${pkgName}" < "${asts}" > typed.json
            "${storeResult}" typed.json "$out"
          ''
