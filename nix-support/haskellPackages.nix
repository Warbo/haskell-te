{ superHaskellPackages, nixFromCabal }:

superHaskellPackages.override {
  overrides = self: super:
    # Use nixFromCabal on paths in ../packages
    let cabalPath = p: self.callPackage (nixFromCabal (toString p) null) {};
     in { ArbitraryHaskell  = cabalPath ../packages/arbitrary-haskell;
          AstPlugin         = cabalPath ../packages/ast-plugin;
          getDeps           = cabalPath ../packages/get-deps;
          HS2AST            = cabalPath ../packages/hs2ast;
          ifcxt             = cabalPath ../packages/ifcxt;
          ML4HSFE           = cabalPath ../packages/ml4hsfe;
          mlspec            = cabalPath ../packages/mlspec;
          mlspec-bench      = cabalPath ../packages/mlspec-bench;
          mlspec-helper     = cabalPath ../packages/mlspec-helper;
          nix-eval          = builtins.trace "FIXME: Don't run hindent unless debug enabled"
                                cabalPath ../packages/nix-eval;
          order-deps        = cabalPath ../packages/order-deps;
          reduce-equations  = builtins.trace "FIXME: Allow reducing custom types"
                                cabalPath ../packages/reduce-equations;
          runtime-arbitrary = cabalPath ../packages/runtime-arbitrary;
        };
  }
