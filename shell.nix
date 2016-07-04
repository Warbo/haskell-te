# Cache packages, so they don't get rebuilt; the line between packages and
# results is blurry
let pkgs = import <nixpkgs> {};
    defs = import ./nix-support pkgs;
 in pkgs.buildEnv {
      name  = "haskell-te";
      paths = with defs; [
        jq
        gnutar
        reduce-equations
        utillinux
        getDeps
        coreutils
        wget
        bc
        ml4hs
        ML4HSFE
        weka
        jre
        mlspec
        nix
        order-deps
        pv
        haskellPackages.cabal2nix
        haskellPackages.cabal-install
        gnuplot
        file
        AstPlugin
        mlspec-bench
      ];
    }
