# Custom definitions
{ callPackage, haskellPackages, buildEnv, real }:
rec {
  annotatedb           = callPackage ../packages/annotatedb       {
                           inherit getDeps;
                         };
  cabal2db             = callPackage ../packages/cabal2db         {};
  explore-theories     = callPackage ../packages/explore-theories {};
  ml4hs                = callPackage ../packages/ml4hs            {};
  dumpToNix            = callPackage ./dumpToNix.nix              {
                           inherit cabal2db;
                         };
  annotateAsts         = callPackage ./annotateAsts.nix           {
                           inherit annotatedb;
                         };
  dumpAndAnnotate      = callPackage ./dumpAndAnnotate.nix        {
                           inherit dumpToNix annotateAsts;
                         };
  recurrent-clustering = callPackage ../packages/recurrent-clustering {
                           inherit order-deps ML4HSFE annotatedb;
                         };

  haskell-te = buildEnv {
    name = "haskell-te";
    paths = [
      # Our custom packages
      annotatedb cabal2db explore-theories getDeps ML4HSFE mlspec-bench
      mlspec order-deps recurrent-clustering ml4hs

      # Standard utilities we need
      real.bash real.cabal-install real.cabal2nix real.coreutils
      real.findutils real.gnugrep real.gnused real.jq real.nix real.time
      real.utillinux
    ];
  };

  # Include our overridden Haskell packages
  inherit haskellPackages;

  # Pull out Haskell packages (e.g. because they provide executables)
  inherit (haskellPackages) AstPlugin getDeps ML4HSFE mlspec mlspec-bench
                            order-deps;
}
