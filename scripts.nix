{ stdenv, nix, cabal-install, jq, doCheck ? true }:

stdenv.mkDerivation {
  name = "cabal2db";

  # Exclude .git from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git") ./.;

  propagatedBuildInputs = [ nix cabal-install jq ];

  USER_HOME  = builtins.getEnv "HOME";
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";
  inherit doCheck;
  checkPhase = ''
    echo "Running $PWD/test.sh" 1>&2
    HOME="$USER_HOME" ./test.sh
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
