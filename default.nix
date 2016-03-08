{ stdenv, order-deps, ML4HSFE }:

stdenv.mkDerivation {
  name = "recurrent-clustering";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  propagatedBuildInputs = [ (import ./weka-cli.nix) order-deps ML4HSFE ];

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
