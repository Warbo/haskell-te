with import ./nix-support {};

stdenv.mkDerivation {
  inherit quickspecBench;

  name = "haskell-te";
  buildCommand = ''
    source $stdenv/setup

    mkdir -p "$out/bin"

    cp -v "$quickspecBench" "$out/bin"
  '';
}
