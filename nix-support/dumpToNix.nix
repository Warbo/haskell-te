{ bash, checkStderr, explore, fail, haskellPackages, hsNameVersion, jq, lib,
  mkBin, python, runCommand, withDeps, wrap, writeScript }:
with builtins;
with lib;

with rec {
  inherit (haskellPackages) cabal-install;

  # Runs AstPlugin. Requires GHC_PKG to point at a pkg-db containing all of
  # the required dependencies, plus AstPlugin
  runAstPluginRaw = mkBin {
    name   = "runAstPluginRaw";
    paths  = [ bash ];
    script = ''
      #!/usr/bin/env bash
      set -e

      OPTS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

      # NOTE: GHC plugin writes JSON to stderr
      cabal --ghc-options="$OPTS" build
    '';
  };

  # Extract the JSON from runAstPlugin's stderr
  getJson = mkBin {
    name   = "getJson";
    paths  = [ python ];
    script = ''
      #!/usr/bin/env python
      from os         import getenv
      from subprocess import PIPE, Popen
      from sys        import stdout, stderr

      # Run the given command, capturing stdout and stderr
      p = Popen([getenv('CMD')], stdout=PIPE, stderr=PIPE)
      sout, serr = p.communicate()

      # We want any lines beginning with '{' to go to stdout, all else to stderr
      isJson  = lambda l: l.startswith('{')
      notJson = lambda l: not isJson(l)

      stderr.write(sout + '\n')
      stderr.write('\n'.join(filter(notJson, serr.split('\n'))))
      stdout.write('\n'.join(filter(isJson,  serr.split('\n'))))
    '';
  };

  testGetJson = runCommand "testGetJson"
    {
      buildInputs = [ fail getJson ];
      script1     = writeScript "script1" ''
        #!/usr/bin/env bash
        set -e
        echo   stdout1
        echo   stderr1   1>&2
        echo '{stdout2}'
        echo '{stderr2}' 1>&2
        echo   stdout3
        echo   stderr3   1>&2
      '';
    }
    ''
      set -e
      set -o pipefail

      X=$(CMD="$script1" getJson) || fail "Couldn't run getJson"
      [[ "x$X" = 'x{stderr2}' ]]  || fail "Got unexpected output '$X'"

      echo pass > "$out"
    '';

  runAstPlugin = withDeps [ testGetJson ] (mkBin {
    name   = "runAstPlugin";
    paths  = [ getJson jq runAstPluginRaw ];
    vars   = { CMD = "runAstPluginRaw"; };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      getJson | jq -c --argjson nv "$nameVersion" '. + $nv' | jq -s '.'
    '';
  });

  main = mkBin {
    name   = "dumpToNix";
    paths  = [ bash cabal-install checkStderr fail runAstPlugin ];
    script = ''
      #!/usr/bin/env bash
      set -e

      [[ -n "$pName" ]] || fail "Can't dump ASTs without pName"

      cp -r "$1" ./pkgDir
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
        echo "Didn't find '$pName' in ghc-pkg DB, trying others" 1>&2

        # Not found in DB. Maybe broken nix-shell nesting, try elsewhere in PATH.
        while read -r DIR
        do
          # Ignore entries which don't contain ghc-pkg
          [[ -e "$DIR/ghc-pkg" ]] || continue

          # Ignore ghc-pkg entries which don't contain AstPlugin or $pName
          packageMissing "$DIR/ghc-pkg" && continue

          # If we're here, we've found a ghc-pkg with AstPlugin and $pName
          GHC_PKG=$("$DIR/ghc-pkg" list | head -n 1 | tr -d ':')

          echo "Found ghc-pkg DB at '$GHC_PKG'" 1>&2
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
      runAstPlugin 2> >(checkStderr)
    '';
  };
};

{
  inherit main;

  dumpToNix = { pkgDir }:
    with rec {
      mkDeps = hsPkgs:
        with {
          pkgDeps = if hsPkgs ? "${pName}"
                       then [ hsPkgs."${pName}" ]
                       else [ (hsPkgs.callPackage pkgDir {}) ];
        };
        [ hsPkgs.AstPlugin hsPkgs.mlspec hsPkgs.mlspec-helper hsPkgs.QuickCheck
          hsPkgs.quickspec ] ++ pkgDeps;

      nameVersion = runCommand "hs-name-version.json"
        {
          inherit pName;
          buildInputs = [ hsNameVersion ];
        }
        ''
          hsNameVersion "$pName" > "$out"
        '';

      # Look for a .cabal file and extract the "name:" field
      pName = (haskellPackages.callPackage pkgDir {}).name;
    };
    runCommand "dumpToNix"
      {
        inherit nameVersion pkgDir pName;
        buildInputs = [ main (haskellPackages.ghcWithPackages mkDeps) ];
      }
      ''
        dumpToNix "$pkgDir" > "$out"
      '';
}
