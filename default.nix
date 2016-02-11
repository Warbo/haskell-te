{ stdenv }:

stdenv.mkDerivation {
  name = "explore-theories";
  src = ./.;
  installPhase = ''
    mkdir -p "$out/bin"
    cp -v explore-theories "$out/bin/"
  '';
}
