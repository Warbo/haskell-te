# Make a list of packages suitable for a 'buildInputs' field. We treat Haskell
# packages separately from everything else. The Haskell packages will include:
#
#  - The contents of 'extraHaskellPackages', required for our scripts
#  - The contents of the 'extraHs' argument; use '[]' for none
#  - The cabal package contained at path 'standalone' (requires a 'default.nix'
#    file, e.g. from 'nixFromCabal'); use 'null' for none
#  - Any 'package' fields read from the JSON file 'f'
#
# The non-Haskell packages will include:
#
#  - The contents of extra-packages, required by our scripts
#  - The contents of the 'extraPkgs' argument; use '[]' for none

{ checkHsEnv, extraHaskellPackages, haskellPackages, jq, lib, pkgName,
  runCommand, withDeps }:

{ extraPkgs ? [], extraHs ? [], standalone ? null, f ? null }:
  with rec {
    names     = if standalone == null then [] else [ name ];
    pkgs      = h: if standalone == null || builtins.elem name hsNames
                      then []
                      else [ (pkg h) ];
    name      = assert standalone != null;
                pkgName (pkg haskellPackages).name;
    pkg       = assert standalone != null;
                h: h.callPackage (import standalone) {};
    extras    = [ jq ] ++ extraPkgs;
    hsNames   = lib.unique (map pkgName (extraHaskellPackages ++ extraHs));
    ghcEnv    = (haskellPackages.ghcWithPackages (h: pkgs h ++ (lib.concatMap
                  (n: if builtins.hasAttr n haskellPackages
                         then [ (builtins.getAttr n h) ]
                         else [])
                  hsNames))).override { ignoreCollisions = true; };
    check     = runCommand "checkIfHsPkgsInEnv"
                  { buildInputs = [ ghcEnv ] ++ extras; }
                  ''
                    set -e
                    "${checkHsEnv (hsNames ++ names)}"
                    echo "true" > "$out"
                  '';
  };
  [ (withDeps [ check ] ghcEnv) ] ++ extras
