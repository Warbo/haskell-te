{ jq, runScript, runTypesScript, storeResult }:
asts: pkg: { pkgSrc ? null }:

runScript { buildInputs = [ jq getDeps utillinux ]; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "${asts}" > typed.json
    "${storeResult}" typed.json "$out"
  ''
