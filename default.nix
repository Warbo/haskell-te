{ stdenv }:

stdenv.mkDerivation {
  name = "recurrent-clustering";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  installPhase = ''
    mkdir -p "$out/bin"
    for FILE in recurrentClustering nix_recurrentClustering runWeka extractFeatures
    do
        cp -v "$FILE" "$out/bin/"
    done

    mkdir -p "$out/lib"
    cp -v weka-cli.nix "$out/lib/"

    chmod +x "$out/bin/"*
  '';
}
