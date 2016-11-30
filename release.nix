# Entry point for evaluating/building
let pkgs = import ./nix-support {};
 in {

  tests = import ./nix-support/tests.nix {};

  package = import ./.;

  inherit (pkgs.haskellPackages)
    ArbitraryHaskell runtime-arbitrary nix-eval mlspec-helper ifcxt AstPlugin
    GetDeps HS2AST ML4HSFE;

  inherit (pkgs)
    mlspec reduce-equations runWeka;
}
