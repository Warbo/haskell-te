{ jq, runScript, runTypesScript, storeResult, getDeps, utillinux }:
asts: pkg: { pkgSrc ? null }:

runScript { buildInputs = [ jq getDeps utillinux ]; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "${asts}" > typed.json
    "${storeResult}" typed.json "$out"
  ''
