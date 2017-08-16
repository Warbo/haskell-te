{ bash, checkStderr, runCmd, drvFromScript, explore, haskellPackages,
  hsNameVersion, jq, lib, runCommand, wrap, writeScript }:
with builtins;
with lib;

# Extract ASTs from a Cabal package
{ pkgDir }:

with rec {
  # Look for a .cabal file and extract the "name:" field
  pName = (haskellPackages.callPackage pkgDir {}).name;

  # Runs AstPlugin. Requires OPTIONS to point GHC at a pkg-db containing all of
  # the required dependencies, plus AstPlugin
  runAstPlugin = writeScript "runAstPlugin" ''
    #!/usr/bin/env bash
    set -e

    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

    # NOTE: GHC plugins write to stderr
    cabal --ghc-options="$OPTIONS" build 1> stdout 2> stderr
  '';

  mkDeps = hsPkgs:
    with {
      pkgDeps = if hsPkgs ? "${pName}"
                   then [ hsPkgs."${pName}" ]
                   else [ (hsPkgs.callPackage pkgDir {}) ];
    };
    [ hsPkgs.AstPlugin hsPkgs.mlspec hsPkgs.mlspec-helper hsPkgs.QuickCheck
       hsPkgs.quickspec ] ++ pkgDeps;

  main = wrap {
    name  = "dumpToNix-script";
    paths = [
      bash
      haskellPackages.cabal-install
      (haskellPackages.ghcWithPackages mkDeps)
    ];
    vars   = { inherit checkStderr pkgDir pName runAstPlugin; };
    script = ''
      #!/usr/bin/env bash
      set -e

      cp -r "$pkgDir" ./pkgDir
      chmod +w -R ./pkgDir

      export HOME="$PWD"
      cd ./pkgDir

      function packageMissing {
        for P in "$pName" AstPlugin
        do
          "$1" list "$P" | grep '(no packages)' > /dev/null && return 0
        done
        return 1
      }

      GHC_PKG=""
      if packageMissing "ghc-pkg"
      then
        # Not found in DB. Maybe broken nix-shell nesting, try elsewhere in PATH.
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
          echo "Couldn't find ghc-pkg for AstPlugin & '$pName'" 1>&2
          exit 1
        fi
      else
        GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
      fi

      export GHC_PKG

      cabal configure --package-db="$GHC_PKG" 1>&2
      "$runAstPlugin" 2> >("$checkStderr") > "$out"
    '';
  };

  nameVersion = runCommand "hs-name-version.json"
    {
      inherit pName;
      buildInputs = [ hsNameVersion ];
    }
    ''
      hsNameVersion "$pName" > "$out"
    '';
};

runCommand "dumpToNix"
  {
    inherit main nameVersion;
    buildInputs = [ jq ];
  }
  ''
    "$main"

    cd pkgDir

    # Send non-JSON to stderr, since it's probably progress/error info
    cat stdout stderr | grep -v "^{" 1>&2 || true

    # Capture all JSON lines
    function getOut() {
      cat stdout stderr                                  |
        grep "^{"                                        |
        jq -c --slurpfile nv "$nameVersion" '. + $nv[0]' |
        jq -s '.' || true
    }
    getOut > "$out"
  ''
