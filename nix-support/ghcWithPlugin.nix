self: dir: name: with builtins; with self;

let mkDeps = hsPkgs: let defDeps = [
                           hsPkgs.quickspec  # For `fun0`, `fun1`, etc.
                           hsPkgs.QuickCheck # For `monomorphise`
                           hsPkgs.AstPlugin  # For AST extraction
                           hsPkgs.mlspec
                           hsPkgs.mlspec-helper
                         ];
                         uncache = dir // { inherit currentTime; };
                         pkgDeps = if hsPkgs ? "${name}"
                                      then [hsPkgs."${name}"]
                                      else [uncache];
                      in defDeps ++ pkgDeps;
in [ jq haskellPackages.cabal-install (haskellPackages.ghcWithPackages mkDeps) ]
