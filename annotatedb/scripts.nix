{ stdenv, jq, getDeps, utillinux }:

stdenv.mkDerivation {
  name = "annotatedb";

  # Exclude .git and test-data from being imported into the Nix store
  src = builtins.filterSource (path: type:
    baseNameOf path != ".git") ./.;

  propagatedBuildInputs = [ jq getDeps utillinux ];

  installPhase = ''
    mkdir -p "$out/bin"
    for FILE in annotateAsts annotateDb getArities getDeps getTypes runTypes tagAsts
    do
        cp -v "$FILE" "$out/bin/"
        chmod +x "$out/bin"
    done
  '';
}
