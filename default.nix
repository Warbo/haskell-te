{ stdenv, nix, haskellPackages, jq }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git") ./.;

  propagatedBuildInputs = [ nix haskellPackages.cabal-install jq ];

  NIX_REMOTE = "daemon";
  NIX_PATH = builtins.getEnv "NIX_PATH";
  doCheck = builtins.getEnv "NIX_DO_CHECK" != "0";
  checkPhase = ''
    echo "Running $PWD/test.sh" 1>&2
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
    for F in *.nix
    do
        cp -v "$F" "$out/lib/"
    done

    chmod +x "$out/bin/"*
  '';
}
