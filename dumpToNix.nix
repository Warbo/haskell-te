{ stdenv, cabal2db }:
pkgDir:

stdenv.mkDerivation {
  inherit pkgDir;
  name = "dump-to-nix-${builtins.hashString "sha256" pkgDir}";
  buildInputs = [ cabal2db ];
  builder = ''
    dump-package "$pkgDir" > "$out"
  '';
}
