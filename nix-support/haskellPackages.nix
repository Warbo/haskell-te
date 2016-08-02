{ extractTarball, fetchgit, fetchurl, nixFromCabal, superHaskellPackages }:

with builtins;

assert let got    = superHaskellPackages.ghc.version;
           should = "7.10.3";
        in addErrorContext "Using GHC ${got} (should be ${should})"
                           (got == should);

superHaskellPackages.override {
  overrides = self: super:
    # Use nixFromCabal on paths in ../packages
    let cabalPath  = p: self.callPackage (nixFromCabal (toString p) null) {};
        cabalCheck = name: given: fallback: cabalPath (if havePath name
                                                          then given
                                                          else fallback);
     in { ArbitraryHaskell  = cabalCheck "arbitrary-haskell"
                                         <arbitrary-haskell>
                                         ../packages/arbitrary-haskell;

          AstPlugin         = cabalCheck "ast-plugin"
                                         <ast-plugin>
                                         ../packages/ast-plugin;

          bench             = cabalPath (extractTarball (fetchurl {
                                url    = https://github.com/Gabriel439/bench/archive/1.0.1.tar.gz;
                                sha256 = "1amfq2jhwxzy34gyqyvanc46admwlfqs9dk3d7c10aivbl7v1kyb";
                              }));

          getDeps           = cabalCheck "get-deps"
                                         <get-deps>
                                         ../packages/get-deps;

          HS2AST            = cabalCheck "hs2ast"
                                         <hs2ast>
                                         ../packages/hs2ast;

          ifcxt             = cabalCheck "ifcxt"
                                         <ifcxt>
                                         ../packages/ifcxt;

          ML4HSFE           = cabalCheck "ml4hsfe"
                                         <ml4hsfe>
                                         ../packages/ml4hsfe;

          mlspec            = cabalCheck "mlspec"
                                         <mlspec>
                                         ../packages/mlspec;

          mlspec-bench      = trace "FIXME: Use bench"
                                (cabalCheck "mlspec-bench"
                                            <mlspec-bench>
                                            ../packages/mlspec-bench);

          mlspec-helper     = cabalCheck "mlspec-helper"
                                         <mlspec-helper>
                                         ../packages/mlspec-helper;

          nix-eval          = trace "FIXME: Don't run hindent unless debug enabled"
                                (cabalCheck "nix-eval"
                                            <nix-eval>
                                            ../packages/nix-eval);

          reduce-equations  = trace "FIXME: Allow reducing custom types"
                                (cabalCheck "reduce-equations"
                                            <reduce-equations>
                                            ../packages/reduce-equations);

          runtime-arbitrary = cabalCheck "runtime-arbitrary"
                                         <runtime-arbitrary>
                                         ../packages/runtime-arbitrary;

          weigh             = cabalPath (fetchgit {
                                url    = https://github.com/fpco/weigh.git;
                                rev    = "26f8e3e";
                                sha256 = "0pmkzlcjfqi41qmrgjyw1y7naclq86kb6mp0i4ni3d1lkiylb9gc";
                              });
        };
  }
