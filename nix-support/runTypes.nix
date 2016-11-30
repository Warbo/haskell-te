{ drvFromScript, runTypesScript, GetDeps }:
asts: { pkgSrc }:

drvFromScript { inherit asts; } ''
    set -e
    "${runTypesScript { inherit pkgSrc; }}" < "$asts" > "$out"
  ''
