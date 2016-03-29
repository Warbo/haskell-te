{ stdenv, nix, haskellPackages, jq }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  propagatedBuildInputs = [ nix haskellPackages.cabal-install jq ];

  NIX_REMOTE = "daemon";
  NIX_PATH = builtins.getEnv "NIX_PATH";
  doCheck = builtins.getEnv "NIX_DO_CHECK" != "0";
  checkPhase = ''
    ./test.sh
  '';

  installPhase = ''
    mkdir -p "$out/bin"

    for CMD in dump-format dump-hackage dump-package dump-package-env \
               dump-package-name runAstPlugin
    do
        cp -v "$CMD" "$out/bin/"
    done

    mkdir -p "$out/lib"
    cp -v ghcWithPlugin.nix "$out/lib/"

    chmod +x "$out/bin/"*
  '';
}
