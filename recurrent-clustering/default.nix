{ stdenv, jq, order-deps, ML4HSFE, nix }:

builtins.trace "FIXME: is recurrent-clustering/default.nix needed?" stdenv.mkDerivation {
  name = "recurrent-clustering";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git" &&
    baseNameOf path != "test-data") ./.;

  propagatedBuildInputs = [
    (import ./weka-cli.nix)
    order-deps
    ML4HSFE
    nix
    jq
  ];

  installPhase = ''
    mkdir -p "$out/lib"
    cp weka-cli.nix "$out/lib/"
  '';
}
