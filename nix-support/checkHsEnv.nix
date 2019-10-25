# Check that the required Haskell packages are found in the environment
{ bash, extraHaskellPackages, fail, haskellPackages, jq, runCommand, unlines,
  withDeps, wrap, writeScript }:

with builtins;
with rec {
  findHsPkgReferences = wrap {
    name = "unique-references";
    vars = {
      hsPkgNames = writeScript "haskell-names"
                     (unlines (builtins.attrNames haskellPackages));

      extractionScript = writeScript "find-references" ''
        #!${bash}/bin/bash
        set -e

        # Allow package names to be given directly, one per line (limit to
        # 128 chars to avoid craziness)
        GOT=$(cat)
        echo "$GOT" | cut -c1-128

        # Take package names from JSON fields. These include:
        #
        #  - Objects with a 'package' field
        #  - Arrays of such objects
        #  - Arrays of arrays of such objects
        #
        # We should be able to ignore dependencies, as they'll be brought in
        # automatically.
        FLATTEN='if type == "array" then .[] else .'
        echo "$GOT" | jq -r "$FLATTEN | $FLATTEN | .package" 2> /dev/null ||
          true
      '';
    };
    script = ''
      INPUT=$(cat | grep '[a-zA-Z_]')
      while read -r NAME
      do
        if grep -xF "$NAME" < "$hsPkgNames" > /dev/null
        then
          echo "$NAME"
        fi
      done < <(echo "$INPUT" | "$extractionScript" | sort -u | grep '^.')
    '';
  };

  go = extra: wrap {
    name = "checkHsEnv";
    vars = {
      inherit findHsPkgReferences;
      allGiven = unlines (extra ++ extraHaskellPackages);
    };
    script = ''
      #!${bash}/bin/bash
      set -e
      set -o pipefail

      function ensurePkg {
        # Skip empty lines
        echo "$1" | grep '[a-zA-Z_]' > /dev/null || return 0

        if ghc-pkg list "$1" | grep "$1" > /dev/null
        then
          return 0
        fi

        echo "Aborting. Didn't find Haskell package '$1' in" 1>&2
        ghc-pkg list 1>&2
        exit 1
      }

      # We must have ghc-pkg, or else we can't even check the others
      command -v "ghc-pkg" > /dev/null 2>&1 || {
        echo "No ghc-pkg command in environment" 1>&2
        exit 1
      }

      # '|| true' to appease 'set -e' when we have no input
      INPUT=""
      [ -t 0 ] || INPUT=$(sort -u | grep "^." | cut -c1-128) || true

      if [[ -n "$INPUT" ]]
      then
        while read -r PKG
        do
          ensurePkg "$PKG"
        done < <(echo "$INPUT"    |
                 grep '[a-zA-Z_]' |
                 "$findHsPkgReferences")
      fi

      while read -r PKG
      do
        ensurePkg "$PKG"
      done < <(echo "$allGiven")

      exit 0
    '';
  };

  test = runCommand "test-checkHsEnv"
    {
      buildInputs = [
        fail
        jq
        ((haskellPackages.ghcWithPackages (h: map (n: getAttr n h)
                                                  extraHaskellPackages)).override {
          ignoreCollisions = true;
        })
      ];
    }
    ''
      #!${bash}/bin/bash
      set -e

      "${go [                                    ]}" || fail "Empty"
      "${go ["text"                              ]}" || fail "text"
      "${go ["text" "containers"                 ]}" || fail "containers"
      "${go ["text" "containers" "parsec"        ]}" || fail "parsec"
      "${go ["text" "containers" "parsec" "aeson"]}" || fail "aeson"

      mkdir "$out"
    '';
};
extra: withDeps [ test ] (go extra)
