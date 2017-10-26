with import ./nix-support {};
stdenv.mkDerivation {
  name        = "haskell-te-benchmark-env";
  src         = ./benchmarkEnv.nix;
  unpackPhase = "true";
  buildInputs = [ asv-nix fail ];
  buildPhase  = ''
    set -e
    fail 'ERROR: Tried building the "benchmarkEnv" derivation. This is not meant
    to be a "real" package: it only provides a build environment, for use with
    nix-shell (e.g. "nix-shell benchmarkEnv.nix")'
  '';
  shellHook   = ''
    echo "Entered benchmarking shell: use 'asv' command to run"
  '';
}
