# Entry point for evaluating/building
let pkgs = builtins.trace "FIXME: Do 64 and 32 bit" import ./nix-support {};
 in {

  tests = import ./nix-support/tests.nix {};

  inherit (pkgs.haskellPackages)
    ArbitraryHaskell runtime-arbitrary nix-eval mlspec-helper ifcxt AstPlugin
    GetDeps HS2AST ML4HSFE;

  inherit (pkgs)
    mlspec mlspec-bench reduce-equations runWeka;

  #tip-eqs = import ./nix-support/exploreTip.nix;
}
