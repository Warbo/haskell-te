{ bash, checkStderr, runCmd, drvFromScript, explore, haskellPackages, lib,
  runScript, wrap, writeScript }:
{ bash, checkStderr, runCmd, drvFromScript, explore, haskellPackages, jq, lib,
  runCommand, wrap, writeScript }:
with builtins;
with lib;

# Extract ASTs from a Cabal package
{ pkgDir }:

let

# Look for a .cabal file and extract the "name:" field
pName = (haskellPackages.callPackage pkgDir {}).name;

# Runs AstPlugin. Requires OPTIONS to point GHC at a pkg-db containing all of
# the required dependencies, plus AstPlugin
runAstPlugin = writeScript "runAstPlugin" ''
  #!/usr/bin/env bash
  set -e

  # NOTE: GHC plugins write to stderr
  cabal --ghc-options="$OPTIONS" build 1> "$TEMPDIR/stdout" 2> "$TEMPDIR/stderr"

  # Send all JSON lines to stdout
  cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" |
    grep "^{" | jq -c ". + {package: \"${pName}\"}" | jq -s '.' || true

  # Send everything else to stderr
  cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" | grep -v "^{" 1>&2 || true
'';

mkDeps = hsPkgs:
  let pkgDeps = if hsPkgs ? "${pName}"
                   then [ hsPkgs."${pName}" ]
                   else [ (hsPkgs.callPackage pkgDir {}) ];
   in [ hsPkgs.quickspec hsPkgs.QuickCheck hsPkgs.AstPlugin
        hsPkgs.mlspec hsPkgs.mlspec-helper ] ++ pkgDeps;

in wrap {
  name  = "dumpToNix";
  paths = [
    bash
    haskellPackages.cabal-install
    (haskellPackages.ghcWithPackages mkDeps)
  ];
  vars  = {
    inherit checkStderr pkgDir runAstPlugin;
    EXTRA_OPTS = "-package AstPlugin -fplugin=AstPlugin.Plugin";
  };
  script = ''
    #!/usr/bin/env bash
    set -e

    cp -r "$pkgDir" ./pkgDir
    chmod +w -R ./pkgDir

    export HOME="$PWD"
    cd ./pkgDir

    function packageMissing {
      for P in "${pName}" AstPlugin
      do
        "$1" list "$P" | grep '(no packages)' > /dev/null && return 0
      done
      return 1
    }

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

    export OPTIONS="-package-db=$GHC_PKG $EXTRA_OPTS"

    "$runAstPlugin" 2> >("$checkStderr" >&2) > "$out"
  '';
}
