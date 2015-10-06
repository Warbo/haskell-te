# Theory Exploration tools for Haskell; packaged for Nix
with import <nixpkgs> {};

# Define some helper functions
let

# Load default version from separate files (makes it easier to programmatically
# replace them)
defaults = name: {
  rev    = import (./components + ("/" + name + ".rev.nix"));
  sha256 = import (./components + ("/" + name + ".sha256.nix"));
};

# Merge or override defaults with given arguments. An sha256 attribute implies
# it's a set of fetchgit arguments.
mkSrc = given: defs: if (given ? sha256)
                     then fetchgit (defs // given)
                     else given;

# Allow package versions (git revisions) to be overridden, so we can reproduce
# old experiments.
in {
  # Haskell packages to use; eg. haskell.packages.ghc784 for GHC 7.8.4
  hsPkgs           ? haskellPackages,

  # Theory Exploration packages. We'll mix and match these for experiments.
  ArbitraryHaskell ? defaults "ArbitraryHaskell",
  AstPlugin        ? defaults "AstPlugin",
  nix-eval         ? defaults "nix-eval",
  getDeps          ? defaults "getDeps",
  HS2AST           ? defaults "HS2AST",
  ml4hs            ? defaults "ml4hs",
  ML4HSFE          ? defaults "ML4HSFE",
  mlspec           ? defaults "mlspec",
  mlspec-helper    ? defaults "mlspec-helper",
  treefeatures     ? defaults "treefeatures"
}:

# Return a set of packages which includes theory exploration tools
(hsPkgs.override { overrides = (self: (super: {

  ArbitraryHaskell = self.callPackage (mkSrc ArbitraryHaskell {
    name = "ArbitraryHaskell";
    url  = http://chriswarbo.net/git/arbitrary-haskell.git;
  }) {};

  AstPlugin = self.callPackage (mkSrc AstPlugin {
    name = "AstPlugin";
    url  =  http://chriswarbo.net/git/ast-plugin.git;
  }) {
    HS2AST = self.HS2AST;
  };

  nix-eval = self.callPackage (mkSrc nix-eval {
    name = "nix-eval";
    url  = http://chriswarbo.net/git/nix-eval.git;
  }) {};

  getDeps = self.callPackage (mkSrc getDeps {
    name  = "getDeps";
    url   = https://github.com/ouanixi/getDeps.git;
  }) {};

  HS2AST = self.callPackage (mkSrc HS2AST {
    name = "HS2AST";
    url  = http://chriswarbo.net/git/hs2ast.git;
  }) {};

  ml4hs  = import (mkSrc ml4hs {
    name = "ml4hs";
    url  = http://chriswarbo.net/git/ml4hs.git;
  });

  mlspec = self.callPackage (mkSrc mlspec {
    name = "mlspec";
    url  = http://chriswarbo.net/git/mlspec.git;
  }) {};

  mlspec-helper = self.callPackage (mkSrc mlspec-helper {
    name = "mlspec-helper";
    url  = http://chriswarbo.net/git/mlspec-helper.git;
  }) {};

  ML4HSFE = self.callPackage (mkSrc ML4HSFE {
    name  = "ML4HSFE";
    url   = http://chriswarbo.net/git/ml4hsfe.git;
  }) {};

  treefeatures = self.callPackage (mkSrc treefeatures {
    name = "tree-features";
    url  = http://chriswarbo.net/git/tree-features.git;
  }) {};

})); })
