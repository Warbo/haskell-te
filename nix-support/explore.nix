{ checkHsEnv, haskellPackages, jq, lib, mkBin, mlspec, nix, nixEnv, pkgName,
  runCommand, timeout, withDeps, writeScript }:
with builtins;
with lib;
with rec {

explore-theories = mkBin {
  name   = "explore-theories";
  paths  = [ jq timeout mlspec nix ];
  vars   = nixEnv;
  script = ''
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

hsPkgsInEnv = env: names: runCommand "checkIfHsPkgsInEnv"
  (env // { cmd = checkHsEnv names; })
  ''
    "$cmd" || exit 1
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
  with rec {
    names     = if standalone == null then [] else [ name ];
    pkgs      = h: if standalone == null || elem name hsNames
                      then []
                      else [ (pkg h) ];
    name      = assert standalone != null; pkgName (pkg haskellPackages).name;
    pkg       = assert standalone != null; h: h.callPackage (import standalone) {};
    extras    = extra-packages ++ extraPkgs;
    hsNames   = unique (map pkgName (extra-haskell-packages ++ extraHs));
    ghcEnv    = haskellPackages.ghcWithPackages (h: pkgs h ++ (concatMap
                  (n: if hasAttr n haskellPackages
                         then [ (getAttr n h) ]
                         else [])
                  hsNames));
    check     = hsPkgsInEnv { buildInputs = [ ghcEnv ] ++ extras; }
                            (hsNames ++ names);
  };
  [ (withDeps [ check ] ghcEnv) ] ++ extras;

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
          extractedEnv;
}
