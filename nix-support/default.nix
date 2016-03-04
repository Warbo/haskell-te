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

          # Wrapper around QuickSpec for theory exploration
          mlspec = cabalPath ../packages/mlspec;

          # Wrapper around Criterion for benchmarking
          mlspec-bench = cabalPath ../packages/mlspec-bench;
        };
    };
    overridden = pkgs // rec {
      # Sets up a Nix environment containing all packages of a theory
      explore-theories = overridden.callPackage ../packages/explore-theories {};

      # Include our overridden Haskell packages
      inherit haskellPackages;

      # Pull out those Haskell packages which provide executable commands
      mlspec       = haskellPackages.mlspec;
      mlspec-bench = haskellPackages.mlspec-bench;
    };
in overridden
