{ stdenv, wget, coreutils }:

# FIXME: Move these away from bash and into Nix
stdenv.mkDerivation {
  name = "haskell-te-scripts";
  propagatedBuildInputs = [ wget coreutils ];
  src  = ../scripts;
  installPhase = ''
    mkdir -p "$out/bin"
    cp *.sh "$out/bin/"
  '';
}
