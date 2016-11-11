# Back-ported from newer nixpkgs
{ cabal2nix, fetchFromGitHub, glibcLocales, haskellPackages, lib, stdenv }:

with lib;
with rec {
  all-cabal-hashes = fetchFromGitHub {
    owner  = "commercialhaskell";
    repo   = "all-cabal-hashes";
    rev    = "ee101d34ff8bd59897aa2eb0a124bcd3fb47ceec";
    sha256 = "1hky0s2c1rv1srfnhbyi3ny14rnfnnp2j9fsr4ylz76xyxgjf5wm";
  };

  hackage2nix = name: version: stdenv.mkDerivation {
    name           = "cabal2nix-${name}-${version}";
    buildInputs    = [ cabal2nix ];
    phases         = ["installPhase"];
    LANG           = "en_US.UTF-8";
    LOCALE_ARCHIVE = lib.optionalString
                       stdenv.isLinux
                       "${glibcLocales}/lib/locale/locale-archive";
    installPhase = ''
      export HOME="$TMP"
      mkdir $out
      hash=$(sed -e 's/.*"SHA256":"//' -e 's/".*$//' ${all-cabal-hashes}/${name}/${version}/${name}.json)
      #cabal2nix --compiler=${haskellPackages.ghc.name} --system=${stdenv.system} --sha256=$hash ${all-cabal-hashes}/${name}/${version}/${name}.cabal >$out/default.nix
      cabal2nix --sha256=$hash ${all-cabal-hashes}/${name}/${version}/${name}.cabal >$out/default.nix
    '';
  };
};

name: version: haskellPackages.callPackage (hackage2nix name version)
