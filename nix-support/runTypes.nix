{ drvFromScript, runTypesScript, GetDeps }:
asts: pkg: { pkgSrc ? null }:

drvFromScript { inherit asts; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "$asts" > "$out"
  ''
