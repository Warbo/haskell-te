# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with rec {
  inherit (nix-config) attrsToDirs wrap;

  qs = quickspecBench.benchVars;
};
attrsToDirs {
  bin = {
    python = wrap {
      paths = [ tipBenchmarks.tools ];
      vars  = {
        NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
        NIX_PATH              =
          "nixpkgs=${toString ./..}/nix-support:real=${toString <nixpkgs>}";

        qsTipSetup  = qs.sampled.genInput;
        qsTipRunner = qs.sampled.runner;

        qsStandaloneMkPkg  = qs.standalone.genAnnotatedPkg;
        qsStandaloneSetup  = qs.standalone.genInput;
        qsStandaloneRunner = qs.standalone.runner;
      };
      script = ''
        #!/usr/bin/env bash
        export theoryFiles='${trace "TODO: Fix quoting in wrap" toJSON {
          list-full  = ./list-full.smt2;
          nat-full   = ./nat-full.smt2;
          nat-simple = ./nat-simple.smt2;
        }}'
        exec "${python}/bin/python" "$@"
      '';
    };
  };
}
