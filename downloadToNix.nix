{ stdenv, haskellPackages }:
pkgName:

let hash = builtins.hashString "sha256" pkgName;
in stdenv.mkDerivation {
  inherit pkgName;
  name        = "download-to-nix-${pkgName}";
  buildInputs = [ haskellPackages.cabal-install ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "download-to-nix-builder" ''
    source "$stdenv/setup"
    cp -rv "$pkgDir" ./pkgDir

    mkdir -p "$out"
    cd "$out"

    export HOME="$TMPDIR"
    cabal get "$pkgName" || exit 1
    for D in ./*
    # */
    do
      mv "$D" source
    done
  '';
}
