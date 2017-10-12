{ runCommand, runTypesScript, withNix }:

asts: { pkgSrc }: runCommand "runTypes" (withNix { inherit asts; }) ''
  set -e
  "${runTypesScript { inherit pkgSrc; }}" < "$asts" > "$out"
''
