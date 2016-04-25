{ adb-scripts, jq, runScript, storeResult }:
asts: pkgName:

runScript { buildInputs = [ adb-scripts jq ]; } ''
  set -e
  runTypes "${pkgName}" < "${asts}" > typed.json
  "${storeResult}" typed.json "$out"
''
