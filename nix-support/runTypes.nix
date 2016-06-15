{ adb-scripts, jq, runScript, runTypesScript, storeResult }:
asts: pkgName:

runScript { buildInputs = [ adb-scripts jq ]; } ''
    set -e
    "${runTypesScript}" "${pkgName}" < "${asts}" > typed.json
    "${storeResult}" typed.json "$out"
  ''
