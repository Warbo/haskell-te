{ benchmark, drvFromScript, explore, haskellPackages, lib, runScript,
  writeScript }:
with builtins;
with lib;

# Extract ASTs from a Cabal package
{ quick, pkgDir }:

let

# Look for a .cabal file and extract the "name:" field
pName = let files = filter (hasSuffix ".cabal")
                           (attrNames (readDir pkgDir));
            cabal = if files == []
                       then abort "Couldn't find name of package in '${pkgDir}'"
                       else head files;
         in runScript { inherit cabal pkgDir; } ''
              grep -i "name[ ]*:" < "$pkgDir/$cabal" |
                cut -d ':' -f 2 | tr -d '[:space:]' > "$out"
            '';

# Runs AstPlugin.
#
# This script makes the following assumptions:
#  - The path to a Cabal project is given as an argument
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg
runAstPlugin = writeScript "runAstPlugin" ''
  #!/usr/bin/env bash
  set -e

  function packageMissing {
    for P in "${pName}" AstPlugin
    do
      "$1" list "$P" | grep '(no packages)' > /dev/null && return 0
    done
    return 1
  }

  function getAsts {
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

    # NOTE: GHC plugins write to stderr
    cabal --ghc-options="$OPTIONS" build 1> "$TEMPDIR/stdout" 2> "$TEMPDIR/stderr"

    # Send all JSON lines to stdout
    cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" | grep    "^{"      || true

    # Send everything else to stderr
    cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" | grep -v "^{" 1>&2 || true
  }

  cd "$1"

  GHC_PKG=""
  if packageMissing "ghc-pkg"
  then
    # Not found in the DB. Maybe broken nix-shell nesting, try elsewhere in PATH
    while read -r DIR
    do
      # Ignore entries which don't contain ghc-pkg
      [[ -e "$DIR/ghc-pkg" ]] || continue

      # Ignore ghc-pkg entries which don't contain AstPlugin or $pName
      packageMissing "$DIR/ghc-pkg" && continue

      # If we're here, we've found a ghc-pkg with AstPlugin and $pName
      GHC_PKG=$("$DIR/ghc-pkg" list | head -n 1 | tr -d ':')
      break
    done < <(echo "$PATH" | tr ':' '\n' | grep ghc)

    if [[ -z "$GHC_PKG" ]]
    then
      echo "Couldn't find ghc-pkg for AstPlugin & '${pName}'" 1>&2
      exit 1
    fi
  else
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
  fi

  cabal configure --package-db="$GHC_PKG" 1>&2

  getAsts | jq -c ". + {package: \"${pName}\"}" | jq -s '.'
'';

mkDeps = hsPkgs:
  let pkgDeps = if hsPkgs ? "${pName}"
                   then [ hsPkgs."${pName}" ]
                   else [ (pkgDir // { inherit currentTime; }) ];
   in [ hsPkgs.quickspec hsPkgs.QuickCheck hsPkgs.AstPlugin
        hsPkgs.mlspec hsPkgs.mlspec-helper ] ++ pkgDeps;

in drvFromScript
  {
    inherit pkgDir;
    buildInputs = [ haskellPackages.cabal-install
                    (haskellPackages.ghcWithPackages mkDeps) ];
  }
  ''
    set -e

    [[ -d "$pkgDir" ]] || {
      echo "Couldn't find directory to dump '$pkgDir'" 1>&2
      exit 1
    }

    cp -r "$pkgDir" ./pkgDir
    chmod +w -R pkgDir

    echo "Dumping '$pkgDir'" 1>&2
    HOME="$PWD" DIR="$PWD/pkgDir" \
      "${benchmark {
           inherit quick;
           cmd = writeScript "dump-package" ''
                   #!/usr/bin/env bash
                   set -e
                   "${runAstPlugin}" "$DIR"
                 '';
       }}" > "$out"
  ''
