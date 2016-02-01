{ stdenv }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  installPhase = ''
    mkdir -p "$out/bin"
    cp -v dump-hackage "$out/bin/"
    cp -v runAstPlugin "$out/bin/"
    cp -v dump-package "$out/bin/"

    mkdir -p "$out/lib"
    cp -v ghcWithPlugin.nix "$out/lib/"

    chmod +x "$out/bin/"*
  '';
}
