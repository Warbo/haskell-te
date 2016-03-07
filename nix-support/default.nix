# A drop-in replacement for <nixpkgs>
args:

let real = import <real> args; # <real> should point to the 'real' <nixpkgs>

    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'pkgs.pristine'
    pkgs = if real ? pristine then real.pristine else real;

    # Turns Haskell project directories into Nix packages
    nixFromCabal = import ./nixFromCabal.nix;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = pkgs.haskellPackages.override {
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

          # Wrapper around QuickSpec for theory exploration
          mlspec = cabalPath ../packages/mlspec;

          # Wrapper around Criterion for benchmarking
          mlspec-bench = cabalPath ../packages/mlspec-bench;

          # Helper functions for use inside MLSpec's nix-eval environments
          mlspec-helper = cabalPath ../packages/mlspec-helper;

          # "eval" for Haskell, using Nix to fetch dependencies
          nix-eval = cabalPath ../packages/nix-eval;

          # Look up instances of 'Arbitrary' at runtime rather than compile time
          runtime-arbitrary = cabalPath ../packages/runtime-arbitrary;
        };
    };
    overridden = pkgs // rec {
      # Post-process extracted ASTs to determine types, arity, etc.
      annotatedb = overridden.callPackage ../packages/annotatedb {};

      # Extracts ASTs from Cabal packages
      cabal2db = overridden.callPackage ../packages/cabal2db {};

      # Sets up a Nix environment containing all packages of a theory
      explore-theories = overridden.callPackage ../packages/explore-theories {};

      # Include our overridden Haskell packages
      inherit haskellPackages;

      # Pull out Haskell packages
      AstPlugin    = haskellPackages.AstPlugin;
      getDeps      = haskellPackages.getDeps;
      mlspec       = haskellPackages.mlspec;
      mlspec-bench = haskellPackages.mlspec-bench;
    };
in overridden
