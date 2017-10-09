{ drvFromScript, runTypesScript }:
asts: { pkgSrc }:

drvFromScript { inherit asts; } ''
    set -e
    "${runTypesScript { inherit pkgSrc; }}" < "$asts" > "$out"
  ''
