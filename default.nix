# Theory Exploration tools for Haskell; packaged for Nix
with import <nixpkgs> {};

# Allow package versions (git revisions) to be overridden, so we can reproduce
# old experiments
{
  # Haskell packages to use; eg. haskell.packages.ghc784 for GHC 7.8.4
  hsPkgs ? haskellPackages,

  hipspec ? {
    rev    = "19e11613fc";
    sha256 = "0m0kmkjn6w2h4d62swnhzj6la8041mvvcm2sachbng5hzkw6l8hf";
  },
  treefeatures ? {
    rev = "1bc0397";
    sha256 = "1w71h7b1i91fdbxv62m3cbq045n1fdfp54h6bra2ccdj2snibx3y";
  },
  HS2AST ? {
    rev = "73248d8";
    sha256 = "1i1grck4zq1pjj1jvvy26lw8wizbwh3hj4vsvr3z216ahlj7bkn3";
  },
  ml4hs ? {
    rev = "8780955";
    sha256 = "1sl7hliv51ijnay5jqp11pwq1iqdfbkw5pf9lgi1fdb580n6blpm";
  },
  mlspec ? {
    rev = "e6504e5";
    sha256 = "0aswp05i524swrvd950dqyl1361bdjmhl0hdqfz8j0xyjif57nmf";
  },
  ArbitraryHaskell ? {
    rev = "f2a2207";
    sha256 = "0jjybdbf5k9fivqx3agcridzslq6b9a69fyjw1zhvvkk1npy9316";
  },
  AstPlugin ? {
    rev = "7c5d495";
    sha256 = "1da90hxwscgigak5jfjbzf9dyvc546dw4qm80rqcjilf7m7aic0x";
  }
}:

# Define some helper functions

let # Generates a .nix file from a .cabal file, using the cabal2nix command
    # preConfig and preInstall are run before and after cabal2nix
    # cbl tells cabal2nix where to look (see cabal2nix documentation)
    nixFromCabal = {name, src, preConfig ? "", preInstall? "", cbl? "."}:
      stdenv.mkDerivation {
        inherit name src;
        buildInputs    = [ haskellPackages.cabal2nix ];
        configurePhase = ''
          (${preConfig}
           cabal2nix ${cbl} > default.nix)
        '';
        installPhase = ''
          (${preInstall}
           cp -r . "$out")
        '';
      };

    # Script to strip non-ASCII chars from .cabal files (they kill cabal2nix)
    asciifyCabal = ''
      for cbl in *.cabal
      do
        NAME=$(basename "$cbl" .cabal)
        mv "$cbl" "$NAME.nonascii"
        tr -cd '[:print:][:cntrl:]' < "$NAME.nonascii" > "$cbl"
      done
    '';

    # Merge or override defaults with given arguments
    mkSrc = given: defs: if (given ? sha256)
                         then fetchgit (defs // given)
                         else given;

# Return a set of packages which includes theory exploration tools
in (hsPkgs.override { overrides = (self: (super: {
  # DEPENDENCIES

  # We need < 0.16
  haskell-src-exts = self.callPackage (import ./haskell-src-exts.nix) {};

  # Hackage version is buggy
  structural-induction = haskell.lib.dontCheck (self.callPackage (nixFromCabal {
    name = "structural-induction-src";
    src  = fetchgit {
      url    = "https://github.com/danr/structural-induction.git";
      rev    = "f487a8225e";
      sha256 = "17f5v0xc9lh5505387qws8q2ffsga6435jqm0dgm9rmpx7429wbh";
    };
    preConfig = asciifyCabal;
  }) {});

  ArbitraryHaskell = self.callPackage (mkSrc ArbitraryHaskell {
    url = "http://chriswarbo.net/git/arbitrary-haskell.git";
  }) {};

  # THEORY EXPLORATION TOOLS (uses "//" to merge in version arguments)

  hipspec = self.callPackage (nixFromCabal {
    name = "hipspec-src";
    src  = mkSrc hipspec {
      name   = "hipspec-src";
      url    = https://github.com/danr/hipspec.git;
    };
    preConfig = asciifyCabal;
  }) {};

  treefeatures = self.callPackage (mkSrc treefeatures {
    name = "tree-features";
    url  = http://chriswarbo.net/git/tree-features.git;
  }) {};

  HS2AST = self.callPackage (mkSrc HS2AST {
    name = "HS2AST";
    url  = http://chriswarbo.net/git/hs2ast.git;
  }) {};

  ml4hs = import (mkSrc ml4hs {
    name = "ml4hs";
    url  = http://chriswarbo.net/git/ml4hs.git;
  });

  mlspec = self.callPackage (mkSrc mlspec {
    name   = "mlspec";
    url    = http://chriswarbo.net/git/mlspec.git;
  }) {};

  AstPlugin = self.callPackage (mkSrc AstPlugin {
    name = "AstPlugin";
    url  =  http://chriswarbo.net/git/ast-plugin.git;
  }) {
    HS2AST = self.HS2AST;
  };
})); })
