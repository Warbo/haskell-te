{ stdenv, order-deps, ML4HSFE, nix, annotatedb }:

stdenv.mkDerivation {
  name = "recurrent-clustering";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  buildInputs = [ annotatedb ];

  propagatedBuildInputs = [
    (import ./weka-cli.nix)
    order-deps
    ML4HSFE
    nix
  ];

  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";
  doCheck    = true;
  checkPhase = ''
    ./test.sh
  '';

  installPhase = ''
    mkdir -p "$out/bin"
    for FILE in recurrentClustering nix_recurrentClustering runWeka cluster
    do
        cp -v "$FILE" "$out/bin/"
    done

    mkdir -p "$out/lib"
    cp -v weka-cli.nix "$out/lib/"

    chmod +x "$out/bin/"*
  '';
}
