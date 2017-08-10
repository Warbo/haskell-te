# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with rec {
  inherit (nix-config) attrsToDirs wrap;

  qs = quickspecBench.benchVars;

  hs = hashspecBench.benchVars;

  ml = mlspecBench.benchVars;

  py = nixpkgs-2016-09.python.withPackages (p: [ p.sexpdata p.subprocess32 ]);
};
attrsToDirs {
  bin = {
    python = wrap {
      name  = "benchmark-python-runner";
      paths = [ tipBenchmarks.tools py ];
      vars  = {
        NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
        NIX_PATH              =
          "nixpkgs=${toString ./..}/nix-support:real=${toString <nixpkgs>}";

        qsTipSetup  = qs.sampled.genInput;
        qsTipRunner = qs.sampled.runner;

        hsTipSetup  = hs.sampled.genInput;
        hsTipRunner = hs.sampled.runner;

        mlTipSetup  = ml.sampled.genInput;
        mlTipRunner = ml.sampled.runner;

        qsStandaloneMkPkg  = qs.standalone.genAnnotatedPkg;
        qsStandaloneSetup  = qs.standalone.genInput;
        qsStandaloneRunner = qs.standalone.runner;

        theoryFiles = toJSON {
          list-full  = ./list-full.smt2;
          nat-full   = ./nat-full.smt2;
          nat-simple = ./nat-simple.smt2;
        };

        theoryTruths = toJSON {
          list-full  = ./ground-truth/list-full.smt2;
          nat-full   = ./ground-truth/nat-full.smt2;
          nat-simple = ./ground-truth/nat-simple.smt2;
        };
      };
      script = ''
        #!/usr/bin/env bash
        exec python "$@"
      '';
    };
  };
}
