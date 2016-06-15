{ stdenv, jq, getDeps, utillinux }:

builtins.trace "FIXME: Get rid of annotatedb/scripts.nix" stdenv.mkDerivation {
  name = "annotatedb";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git") ./.;

  propagatedBuildInputs = [ jq getDeps utillinux ];

  installPhase = ''
    mkdir -p "$out/bin"
  '';
}
