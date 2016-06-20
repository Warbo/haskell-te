with import <nixpkgs> {};
with builtins;

name:

let mkDeps = hsPkgs: let defDeps = [
                           hsPkgs.quickspec  # For `fun0`, `fun1`, etc.
                           hsPkgs.QuickCheck # For `monomorphise`
                           hsPkgs.AstPlugin  # For AST extraction
                         ];
                         fromEnv = hsPkgs.callPackage
                                     (import (getEnv "DIR")) {};
                         uncache = fromEnv // { inherit currentTime; };
                         pkgDeps = if hsPkgs ? "${name}"
                                      then [hsPkgs."${name}"]
                                      else [uncache];
                      in defDeps ++ pkgDeps;
 in runCommand "dummy" {
      buildInputs = [
        jq
        haskellPackages.cabal-install
        (haskellPackages.ghcWithPackages mkDeps)
      ];
    } ""
