# A drop-in replacement for <nixpkgs>
args:


let real = import <real> args; # <real> should point to the 'real' <nixpkgs>

    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'pkgs.pristine'
    pkgs = if real ? pristine then real.pristine else real;

    # Turns Haskell project directories into Nix packages
    nixFromCabal    = import ./nixFromCabal.nix;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = pkgs.haskellPackages.override {
      overrides = self: super: {
        # Wrapper around Criterion for benchmarking
        mlspec-bench = self.callPackage (nixFromCabal (toString ../packages/mlspec-bench) null) {};

        # Wrapper around QuickSpec for theory exploration
        mlspec       = self.callPackage (nixFromCabal (toString ../packages/mlspec) null) {};
      };
    };
    overridden = pkgs // rec {
      # Sets up a Nix environment containing all packages of a theory
      explore-theories = overridden.callPackage ../packages/explore-theories {};
      mlspec-bench = haskellPackages.mlspec-bench;
      mlspec = haskellPackages.mlspec;
      inherit haskellPackages;
    };
in overridden
