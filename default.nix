with import <nixpkgs> {};

    # Generate a .nix file from a .cabal file, by calling the cabal2nix command
let nixFromCabal = {name, src, preConfig ? "", preInstall? "", cbl? "."}:
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
  QuickCheck = self.callPackage (nixFromCabal {
    name = "quickcheck-src";
    src  = fetchgit {
      url    = https://github.com/nick8325/quickcheck.git;
      rev    = "98766f5fbe";
      sha256 = "0vz33adwpjfakj0hq8wlsclf6jhg59f6aa5qdyg5wxzn2fd3j0fg";
    };
    preConfig = asciifyCabal;
  }) {};

  hipspec = hsTools.doJailbreak (self.callPackage (nixFromCabal {
    name = "hipspec-src";
    src  = fetchgit {
      name   = "hipspec-src";
      #url    = https://github.com/danr/hipspec.git;
      url    =  /home/chris/Programming/Haskell/hipspec;
      rev    = "a695769";
      sha256 = "0f7wzpapzrm1z22437fqgz3pg96xb9mgbpq4snxbj5hg1h2dpwbd";
    };
    preConfig = asciifyCabal;
  }) {});

  hipspecifyer = self.callPackage (nixFromCabal {
    name = "hipspecifyer-src";
    src  = fetchgit {
      url    = "https://github.com/moajohansson/IsaHipster.git";
      rev    = "ec44cfa";
      sha256 = "0605g8py6kwrkbjahhkl0pmlbz8q46sfcahxjpijsl0i3mafwjf3";
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

  unification-fd = self.callPackage (import ./unification-fd.nix) {};
})); }
