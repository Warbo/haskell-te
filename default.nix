{ stdenv }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  installPhase = ''
    mkdir -p "$out/bin"
    cp dump-hackage "$out/bin/"
    cp runAstPlugin "$out/bin/"

    mkdir -p "$out/lib"
    cp ghcWithPlugin.nix "$out/lib/"

    echo "Patching to use '$out/lib/ghcWithPlugin.nix'"
    sed -e "s@./ghcWithPlugin.nix@$out/lib/ghcWithPlugin.nix@g" < dump-package > "$out/bin/dump-package"

    chmod +x "$out/bin/"*
  '';
}
