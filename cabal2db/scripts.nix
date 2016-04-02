{ stdenv, nix, cabal-install, jq }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git") ./.;

  propagatedBuildInputs = [ nix cabal-install jq ];

  installPhase = ''
    mkdir -p "$out/bin"

    for CMD in dump-format dump-hackage dump-package dump-package-env \
               dump-package-name runAstPlugin
    do
        cp "$CMD" "$out/bin/"
    done

    mkdir -p "$out/lib"
    for F in *.nix
    do
        cp "$F" "$out/lib/"
    done

    chmod +x "$out/bin/"*
  '';
}
