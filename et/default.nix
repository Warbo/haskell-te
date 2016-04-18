{ stdenv }:

stdenv.mkDerivation {
  name = "explore-theories";
  src = ./.;
  installPhase = ''
    mkdir -p "$out/bin"
    for F in build-env explore-theories extra-haskell-packages extra-packages path-to-front
    do
        cp -v "$F" "$out/bin/"
        chmod +x "$out/bin/$F"
    done
  '';
}
