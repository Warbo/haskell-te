{ checkHsEnv, drvFromScript, haskellPackageNames, haskellPackages, jq, lib,
  mkBin, mlspec, pkgName, timeout, writeScript }:
with builtins;
with lib;
with rec {

explore-theories = mkBin {
  name   = "explore-theories";
  paths  = [ jq timeout ];
  script =  ''
    #!/usr/bin/env bash
    set -e
    set -o pipefail

    function noDepth {
      grep -v "^Depth" || true # Don't abort if nothing found
    }

    function checkForErrors {
      while read -r LINE
      do
        echo "$LINE"
        if echo "$LINE" | grep "No instance for" > /dev/null
        then
          echo "Haskell error, aborting" 1>&2
          exit 1
        fi
      done
    }

    # limit time/memory using 'timeout'
    withTimeout MLSpec "$@" 2> >(checkForErrors 1>&2) | noDepth | jq -s '.'
  '';
};

findHsPkgReferences =
  let extractionScript = writeScript "find-references" ''
        # Allow package names to be given directly, one per line (limit to 128
        # chars to avoid craziness)
        INPUT=$(cat)
        echo "$INPUT" | cut -c1-128

        # Take package names from JSON fields. These include:
        #
        #  - Objects with a 'package' field
        #  - Arrays of such objects
        #  - Arrays of arrays of such objects
        #
        # We should be able to ignore dependencies, as they'll be brought in
        # automatically.
        FLATTEN='if type == "array" then .[] else .'
        echo "$INPUT" | jq -r "$FLATTEN | $FLATTEN | .package" 2> /dev/null ||
          true
      '';
   in writeScript "unique-references" ''
        INPUT=$(cat | grep '[a-zA-Z_]')
        while read -r NAME
        do
          if grep -xF "$NAME" < "${haskellPackageNames}" > /dev/null
          then
            echo "$NAME"
          fi
        done < <(echo "$INPUT" | "${extractionScript}" | sort -u | grep '^.')
      '';

hsPkgsInEnv = env: names:
  drvFromScript env ''
    "${checkHsEnv names}" || exit 1
    echo "true" > "$out"
  '';

# Make a list of packages suitable for a 'buildInputs' field. We treat Haskell
# packages separately from everything else. The Haskell packages will include:
#
#  - The contents of 'extra-haskell-packages', required for our scripts
#  - The contents of the 'extraHs' argument; use '[]' for none
#  - The cabal package contained at path 'standalone' (requires a 'default.nix'
#    file, e.g. from 'nixFromCabal'); use 'null' for none
#  - Any 'package' fields read from the JSON file 'f'
#
# The non-Haskell packages will include:
#
#  - The contents of extra-packages, required by our scripts
#  - The contents of the 'extraPkgs' argument; use '[]' for none
#
extractedEnv = { extraPkgs ? [], extraHs ? [], standalone ? null, f ? null }:
      # Use a variety of extra settings when 'standalone' is given
  let attrs   = if standalone != null &&
                   pathExists (unsafeDiscardStringContext
                                 "${toString standalone}/default.nix")
                   then trace "Including '${toString standalone}'" rec {
                     pkg   = h: h.callPackage (import standalone) {};
                     pkgs  = h: if elem name hsNames
                                   then []
                                   else [ (pkg h) ];
                     name  = pkgName (pkg haskellPackages).name;
                     names = [ name ];
                   }
                   else {
                     pkgs  = h: [];
                     names = [];
                   };
      extracted = [];
      hsNames = unique (map pkgName (extracted ++ extra-haskell-packages ++ extraHs));
      hsPkgs  = h: (concatMap (n: if haskellPackages ? "${n}"
                                     then [ h."${n}" ]
                                     else [          ])
                              hsNames) ++ attrs.pkgs h;
      ps      = [ (haskellPackages.ghcWithPackages hsPkgs) ] ++
                extra-packages ++ extraPkgs;
      # Checks whether all required Haskell packages are found. We add this to
      # our result, so that the environment will be checked during dependency
      # building
      check   = hsPkgsInEnv { buildInputs = ps; } (hsNames ++ attrs.names);
   in ps ++ [ check ];

# Haskell packages required for MLSpec
extra-haskell-packages = [ "mlspec" "mlspec-helper" "runtime-arbitrary"
                           "quickspec" "QuickCheck" "AstPlugin" ];

extra-packages = [ jq ];

exploreEnv = [ (haskellPackages.ghcWithPackages (h: map (n: h."${n}")
                                                    extra-haskell-packages)) ] ++
             extra-packages;
};
{
  inherit extra-haskell-packages explore-theories exploreEnv
          extractedEnv findHsPkgReferences;
}
