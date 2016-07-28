{ benchmark, dump-package, parseJSON, perl, runScript, stdenv, writeScript }:
{ quick, pkgDir }:

let

# Extracts ASTs from a Cabal package
dump-package = writeScript "dump-package" ''
  #!/usr/bin/env bash
  set -e

  [[ -n "$DIR" ]] || DIR="$1"
  [[ -n "$DIR" ]] || {
    echo "Please provide a package directory, either as argument or DIR" 1>&2
    exit 3
  }

  [[ -d "$DIR" ]] || {
    echo "Directory '$DIR' not found" 1>&2
    exit 1
  }

  PKG=$("${dump-package-name}" "$DIR")

  ENV=$(echo "with import <nixpkgs> {}; import \"${ghcWithPlugin}\" \"$PKG\"") || {
    echo "Unable to get package environment; aborting" 1>&2
    exit 2
  }

  nix-shell --show-trace \
            -E "$ENV" \
            --run "'${runAstPlugin}' '$DIR'"
'';

in stdenv.mkDerivation {
     name         = "dumped-asts";
     buildInputs  = [ perl ];
     buildCommand = ''
       source $stdenv/setup
       set -e

       D="${toString pkgDir}"

       [[ -d "$D" ]] || {
         echo "Couldn't find directory to dump '$D'" 1>&2
         exit 1
       }

       cp -r "$D" ./pkgDir
       chmod +w -R pkgDir

       echo "Dumping '$D'" 1>&2
       HOME="$PWD" DIR="$PWD/pkgDir" \
         "${benchmark quick dump-package []}" > "$out"
     '';
   }
