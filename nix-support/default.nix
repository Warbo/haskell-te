# A drop-in replacement for <nixpkgs>
# WATCH OUT! callPackage can introduce references to the underlying <nixpkgs>
# behind your back. If in doubt, pass such arguments explicitly.
args:

let real = import <real> args; # <real> should point to the 'real' <nixpkgs>

    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'original.pristine'
    original = if real ? pristine then real.pristine else real;

    # Turns Haskell project directories into Nix packages
    nixFromCabal = import ./nixFromCabal.nix;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = assert !(original.haskellPackages ? order-deps);
    original.haskellPackages.override {
      overrides = self: super:
        # Use nixFromCabal on paths in ../packages
        let cabalPath = p: self.callPackage (nixFromCabal (toString p) null) {};
         in {
          # Generate arbitrary Haskell code for testing purposes
          ArbitraryHaskell = cabalPath ../packages/arbitrary-haskell;

          # GHC Plugin to extract ASTs from Core
          AstPlugin = cabalPath ../packages/ast-plugin;

          # Extract dependencies from ASTs
          getDeps = cabalPath ../packages/get-deps;

          # Shared library for handling ASTs
          HS2AST = cabalPath ../packages/hs2ast;

          # Feature extraction to go from ASTs to feature vectors
          ML4HSFE = cabalPath ../packages/ml4hsfe;

          # Wrapper around QuickSpec for theory exploration
          mlspec = cabalPath ../packages/mlspec;

          # Wrapper around Criterion for benchmarking
          mlspec-bench = cabalPath ../packages/mlspec-bench;

          # Helper functions for use inside MLSpec's nix-eval environments
          mlspec-helper = cabalPath ../packages/mlspec-helper;

          # "eval" for Haskell, using Nix to fetch dependencies
          nix-eval = cabalPath ../packages/nix-eval;

          # Topologically sort by dependencies
          order-deps = cabalPath ../packages/order-deps;

          # Look up instances of 'Arbitrary' at runtime rather than compile time
          runtime-arbitrary = cabalPath ../packages/runtime-arbitrary;
        };
      };

    overridden = original // {
      # Post-process extracted ASTs to determine types, arity, etc.
      annotatedb = overridden.callPackage ../packages/annotatedb {};

      # Extracts ASTs from Cabal packages
      cabal2db = overridden.callPackage ../packages/cabal2db {};

      # Sets up a Nix environment containing all packages of a theory
      explore-theories = overridden.callPackage ../packages/explore-theories {};

      # Misc scripts
      ml4hs = overridden.callPackage ../packages/ml4hs {};

      # The environment we'll be running in
      haskell-te = overridden.buildEnv {
        name = "haskell-te";
        paths = [
          # Our custom packages
          overridden.annotatedb
          overridden.cabal2db
          overridden.explore-theories
          overridden.getDeps
          overridden.ML4HSFE
          overridden.mlspec-bench
          overridden.order-deps
          overridden.recurrent-clustering
          overridden.ml4hs

          # Standard utilities we need
          real.bash
          real.cabal-install
          real.cabal2nix
          real.coreutils
          real.findutils
          real.gnugrep
          real.gnused
          real.jq
          real.nix
          real.time
        ];
      };

      # Iterative recurrent clustering algorithm
      recurrent-clustering = overridden.callPackage ../packages/recurrent-clustering {};

      # Include our overridden Haskell packages
      inherit haskellPackages;

      # Pull out Haskell packages (e.g. because they provide executables)
      AstPlugin    = overridden.haskellPackages.AstPlugin;
      getDeps      = overridden.haskellPackages.getDeps;
      ML4HSFE      = overridden.haskellPackages.ML4HSFE;
      mlspec       = overridden.haskellPackages.mlspec;
      mlspec-bench = overridden.haskellPackages.mlspec-bench;
      order-deps   = overridden.haskellPackages.order-deps;
    };
in overridden
