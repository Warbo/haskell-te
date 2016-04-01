# Custom definitions
{ bash, buildEnv, coreutils, gnutar, haskellPackages, jq, lib, nix, real,
  runCommand, stdenv, time, writeScript }:
let cabal2db = import ../packages/cabal2db {
                 inherit stdenv haskellPackages nix gnutar jq lib runCommand writeScript;
               };
in with cabal2db;

cabal2db // rec {
  inherit (import ./runBenchmark.nix {
             inherit bash coreutils explore-theories jq lib
                     mlspec-bench time writeScript;
           }) lastEntry withCriterion withTime
                                              benchmark;

  parseJSON            = import ./parseJSON.nix {
                           inherit jq runScript writeScript;
                         };

  annotatedb           = import ../packages/annotatedb       {
                           inherit getDeps;
                         };

  explore-theories     = import ../packages/explore-theories {
                           inherit stdenv;
                         };
  ml4hs                = import ../packages/ml4hs            {};
  dumpToNix            = import ./dumpToNix.nix              {
                           inherit cabal2db;
                         };
  annotateAsts         = import ./annotateAsts.nix           {
                           inherit annotatedb;
                         };
  dumpAndAnnotate      = import ./dumpAndAnnotate.nix        {
                           inherit dumpToNix annotateAsts;
                         };
  recurrent-clustering = import ../packages/recurrent-clustering {
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
