# Theory Exploration tools for Haskell; packaged for Nix

# First we make some helper functions
with import <nixpkgs> {}; let

# Lets us override cabal settings
hsTools = import "${<nixpkgs>}/pkgs/development/haskell-modules/lib.nix" {
  pkgs = import <nixpkgs> {};
};

# Generates a .nix file from a .cabal file, by calling the cabal2nix command
# preConfig and preInstall are shell commands to run before and after cabal2nix
# cbl tells cabal2nix where to read settings from (see cabal2nix documentation)
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

# Shell script to strip non-ASCII chars from .cabal files (they kill cabal2nix)
asciifyCabal = ''
  for cbl in *.cabal
  do
    NAME=$(basename "$cbl" .cabal)
    mv "$cbl" "$NAME.nonascii"
    tr -cd '[:print:][:cntrl:]' < "$NAME.nonascii" > "$cbl"
  done
'';

# Return a function for generating theory exploration packages
in ({
   # Haskell packages to use; eg. haskell.packages.ghc784
  hsPkgs ? haskellPackages,

  # Allow experiments to specify particular versions
  hipspec ? {
    rev    = "19e11613fc";
    sha256 = "0m0kmkjn6w2h4d62swnhzj6la8041mvvcm2sachbng5hzkw6l8hf";
  },
  hipspecifyer ? {
    rev    = "f81eb6d630";
    sha256 = "1hb0mlds91fv3nxc0cppq48zfwcpkk5p2bmix75mmsnichkp8ncc";
  },
  treefeatures ? {
    sha256 = "1w71h7b1i91fdbxv62m3cbq045n1fdfp54h6bra2ccdj2snibx3y";
  },
  hs2ast ? {
    sha256 = "1lg8p0p30dp6pvbi007hlpxk1bnyxhfazzvgyqrx837da43ymm7f";
  },
  ml4hs ? {
    rev    = "2797f11";
    sha256 = "1q27a4ly1f5qqy18gs40ci01cvhxkahrhh6jighk60drprwv0fg1";
  }
}: hsPkgs.override { overrides = (self: (super: {

  # Dependencies: we need these, but don't really care about them

  # We need < 0.16
  haskell-src-exts = self.callPackage (import ./haskell-src-exts.nix) {};

  # Hackage version is buggy
  structural-induction = hsTools.dontCheck (self.callPackage (nixFromCabal {
    name = "structural-induction-src";
    src  = fetchgit {
      url    = "https://github.com/danr/structural-induction.git";
      rev    = "f487a8225e";
      sha256 = "17f5v0xc9lh5505387qws8q2ffsga6435jqm0dgm9rmpx7429wbh";
    };
    preConfig = asciifyCabal;
  }) {});

  # Theory exploration: these are the things we care about

  hipspec = self.callPackage (nixFromCabal {
    name = "hipspec-src";
    src  = fetchgit (hipspec // {
      name   = "hipspec-src";
      url    = https://github.com/danr/hipspec.git;
    });
    preConfig = asciifyCabal;
  }) {};

  hipspecifyer = self.callPackage (nixFromCabal {
    name = "hipspecifyer-src";
    src  = fetchgit (hipspecifyer // {
      url    = https://github.com/moajohansson/IsaHipster.git;
    });
    # The cabal project lives in the "hipspecifyer" directory
    preConfig  = "cd hipspecifyer";
    preInstall = "cd hipspecifyer";
  }) {};

  treefeatures = self.callPackage (fetchgit (treefeatures // {
    name = "tree-features";
    url  = http://chriswarbo.net/git/tree-features.git;
  })) {};

  hs2ast = self.callPackage (fetchgit (hs2ast // {
    name = "hs2ast";
    url  = http://chriswarbo.net/git/hs2ast.git;
  })) {};

  ml4hs = (import (fetchgit (ml4hs // {
    name = "ml4hs";
    url  = http://chriswarbo.net/git/ml4hs.git;
  }))) {
    treefeatures = self.treefeatures;
    hs2ast = self.hs2ast;
  };

})); })
