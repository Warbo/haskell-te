# Back-ported from newer nixpkgs
{ cabal2nix, fetchFromGitHub, glibcLocales, lib, stdenv }:

with lib;
with rec {
  all-cabal-hashes = fetchFromGitHub {
    owner  = "commercialhaskell";
    repo   = "all-cabal-hashes";
    rev    = "1932d9e";
    sha256 = "07036zgxpf7s057qr5jf5wjg17rl3jsrlaxfg15avmfbgrl23fd6";
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
      cabal2nix --sha256=$hash ${all-cabal-hashes}/${name}/${version}/${name}.cabal >$out/default.nix
    '';
  };
};

hackage2nix
