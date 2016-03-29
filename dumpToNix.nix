{ stdenv, cabal2db }:
pkgDir:

let hash = builtins.hashString "sha256" pkgDir;
in stdenv.mkDerivation {
  inherit pkgDir;
  name        = "dump-to-nix-${hash}";
  buildInputs = [ cabal2db ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";
  HOME=builtins.getEnv "HOME";

  # Copy the pkgDir to the store and run dump-package
  builder = builtins.toFile "dump-to-nix-builder-${hash}" ''
    source "$stdenv/setup"
    cp -rv "$pkgDir" ./pkgDir
    chmod +w -R pkgDir

    mkdir -p "$out"
    #HOME="$TMPDIR"
    dump-package pkgDir > "$out/dump.json"
  '';
}
