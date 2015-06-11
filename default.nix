with import <nixpkgs> {};

    # Lets us override cabal settings
let hsTools = import "${<nixpkgs>}/pkgs/development/haskell-modules/lib.nix" {
      pkgs = import <nixpkgs> {};
    };

    # Generate a .nix file from a .cabal file, by calling the cabal2nix command
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

    # Strip non-ASCII characters from .cabal files, to stop cabal2nix choking
    asciifyCabal = ''
      for cbl in *.cabal
      do
        NAME=$(basename "$cbl" .cabal)
        mv "$cbl" "$NAME.nonascii"
        tr -cd '[:print:][:cntrl:]' < "$NAME.nonascii" > "$cbl"
      done
    '';

   # Takes in a set of Haskell packages, returns an augmented set
in haskellPkgs: haskellPkgs.override { overrides = (self: (super: {
  # Ignore QuickCheck < 2.8 requirement
  exceptions = hsTools.doJailbreak haskellPkgs.exceptions;

  # We need >= 2.8
  QuickCheck = self.callPackage (import ./quickcheck.nix) {};

  hipspec = self.callPackage (nixFromCabal {
    name = "hipspec-src";
    src  = fetchgit {
      name   = "hipspec-src";
      url    = https://github.com/danr/hipspec.git;
      rev    = "19e11613fc";
      sha256 = "0m0kmkjn6w2h4d62swnhzj6la8041mvvcm2sachbng5hzkw6l8hf";
    };
    preConfig = asciifyCabal;
  }) {}
  ;

  hipspecifyer = self.callPackage (nixFromCabal {
    name = "hipspecifyer-src";
    src  = fetchgit {
      url    = "https://github.com/moajohansson/IsaHipster.git";
      rev    = "f81eb6d630";
      sha256 = "1hb0mlds91fv3nxc0cppq48zfwcpkk5p2bmix75mmsnichkp8ncc";
    };
    preConfig  = "cd hipspecifyer";
    preInstall = "cd hipspecifyer";
  }) {};

  structural-induction = hsTools.dontCheck (self.callPackage (nixFromCabal {
    name = "structural-induction-src";
    src  = fetchgit {
      url    = "https://github.com/danr/structural-induction.git";
      rev    = "f487a8225e";
      sha256 = "17f5v0xc9lh5505387qws8q2ffsga6435jqm0dgm9rmpx7429wbh";
    };
    preConfig = asciifyCabal;
  }) {});

  haskell-src-exts = self.callPackage (import ./haskell-src-exts.nix) {};
})); }
