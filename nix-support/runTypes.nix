{ adb-scripts, jq, runScript, runTypesScript, storeResult }:
asts: pkg: { pkgSrc ? null }:

runScript { buildInputs = [ adb-scripts jq ]; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "${asts}" > typed.json
    "${storeResult}" typed.json "$out"
  ''
