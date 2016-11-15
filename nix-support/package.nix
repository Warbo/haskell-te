{ buildEnv, makeWrapper, mlspecBench, quickspecBench, stdenv, tipBenchmarks }:

let env = buildEnv {
      name  = "te-env";
      paths = [ tipBenchmarks.tools ];
    };
 in stdenv.mkDerivation {
      name        = "haskell-te";
      buildInputs = [ makeWrapper ];

      buildCommand = ''
        source $stdenv/setup

        mkdir -p "$out/bin"

        makeWrapper ${quickspecBench.script} "$out/bin/quickspecBench" \
          --prefix PATH : "${env}/bin"

        makeWrapper ${mlspecBench.script}    "$out/bin/mlspecBench"    \
          --prefix PATH : "${env}/bin"
      '';
    }
