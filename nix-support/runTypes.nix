{ jq, runScript, runTypesScript, storeResult, GetDeps, utillinux }:
asts: pkg: { pkgSrc ? null }:

runScript { buildInputs = [ GetDeps ]; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "${asts}" > typed.json
    "${storeResult}" typed.json "$out"
  ''
