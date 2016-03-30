{ stdenv, cabal2db, lib }:
pkgDir:

with builtins;
with lib;
let hash = unsafeDiscardStringContext (hashString "sha256" "${pkgDir}");
in stdenv.mkDerivation {
  inherit pkgDir;
  name        = "dump-to-nix-${hash}";
  buildInputs = [ cabal2db ] ++ (if isDerivation pkgDir then [ pkgDir ] else []);

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";
  HOME=builtins.getEnv "HOME";

  # Copy the pkgDir to the store and run dump-package
  builder = builtins.toFile "dump-to-nix-builder-${hash}" ''
    source "$stdenv/setup"
    cp -rv "$pkgDir" ./pkgDir
    chmod +w -R pkgDir

    dump-package "$(readlink -f pkgDir)" > "$out"
  '';
}
