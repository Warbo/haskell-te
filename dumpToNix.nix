{ stdenv, nix, haskellPackages }:
{ pkgDir }:

stdenv.mkDerivation {
  inherit pkgDir;
  name = "dump-to-nix-${builtins.hashString pkgDir}";
  buildInputs = [ (import ./. { inherit stdenv nix haskellPackages; }) ];
  builder = ''
    dump-package "$pkgDir" > "$out"
  '';
}
