with import ./nix-support {};
stdenv.mkDerivation {
  name         = "haskell-te-benchmark-env";
  src          = ./benchmarkEnv.nix;
  unpackPhase  = "true";
  buildInputs  = [ asv-nix fail ];
  installPhase = ''
    set -e
    echo 'WARNING: Building the "benchmarkEnv" derivation. This is not meant
    to be a "real" package: it only provides a build environment, for use with
    nix-shell (e.g. "nix-shell benchmarkEnv.nix")'
    echo "This is not a 'package', it's meant to be used via nix-shell" > "$out"
  '';
  shellHook = ''
    echo "Entered benchmarking shell: use 'asv' command to run"
  '';
}
