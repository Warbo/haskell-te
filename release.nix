let pkgs = import ./nix-support {};
 in {

  tests = import ./nix-support/tests.nix {};

  inherit (pkgs.haskellPackages)
    ArbitraryHaskell runtime-arbitrary nix-eval mlspec-helper ifcxt AstPlugin
    getDeps HS2AST ML4HSFE;

  inherit (pkgs)
    mlspec mlspec-bench order-deps reduce-equations runWeka;

  #tip-eqs = import ./nix-support/exploreTip.nix;
}
