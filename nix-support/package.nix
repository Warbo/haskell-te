{ buildEnv, makeWrapper, quickspecBench, stdenv, tipBenchmarks }:

let env = buildEnv {
      name  = "te-env";
      paths = tipBenchmarks.te-benchmark.propagatedNativeBuildInputs;
    };
 in stdenv.mkDerivation {
      buildInputs = [ makeWrapper ];

      name = "haskell-te";
      buildCommand = ''
        source $stdenv/setup

        mkdir -p "$out/bin"

        makeWrapper ${quickspecBench.script} "$out/bin/quickspecBench" \
          --prefix PATH : "${env}/bin"
      '';
    }
