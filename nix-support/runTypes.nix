{ drvFromScript, runTypesScript, GetDeps }:
asts: pkg: { pkgSrc ? null }:

drvFromScript { inherit asts; buildInputs = [ GetDeps ]; } ''
    set -e
    "${runTypesScript { inherit pkg pkgSrc; }}" < "$asts" > "$out"
  ''
