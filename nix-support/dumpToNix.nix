{ benchmark, dump-package, parseJSON, perl, runScript, stdenv, writeScript }:
{ quick, pkgDir }:

let

dump-package-env = trace "FIXME: dump-package-env should be used by the outer Nix"
  writeScript "dump-package-env" ''
    #!/usr/bin/env bash
    set -e

    [[ "$#" -gt 0 ]] || {
      echo "dump-package-env needs a Cabal project directory" 1>&2
      exit 1
    }

    [[ -d "$1" ]] || {
      echo "Directory '$1' not found" 1>&2
      exit 1
    }

    DIR="$1"
    PKG=$("${dump-package-name}" "$DIR")

    echo "with import <nixpkgs> {}; import \"${ghcWithPlugin}\" \"$PKG\""
  '';

# Extracts ASTs from a Cabal package
dump-package = writeScript "dump-package" ''
  #!/usr/bin/env bash
  set -e

  [[ -n "$DIR" ]] || DIR="$1"
  [[ -n "$DIR" ]] || {
    echo "Please provide a package directory, either as argument or DIR" 1>&2
    exit 3
  }

  ENV=$("${dump-package-env}" "$DIR") || {
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
