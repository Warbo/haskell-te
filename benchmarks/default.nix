# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with rec {
  quickspecTip = callPackage ./quickspecTip.nix {};

  qs = quickspecBench.benchVars;

  hs = hashspecBench.benchVars;

  ml = mlspecBench.benchVars;

  py = nixpkgs-2016-09.python.withPackages (p: [ p.sexpdata p.subprocess32 ]);
};

mkBin {
  name  = "python";
  paths = [ py quickspecTip tipBenchmarks.tools ];
  vars  = nixEnv // {
    NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;

    hsTipSetup  = hs.sampled.genInput;
    hsTipRunner = hs.sampled.runner;

    mlTipSetup  = ml.sampled.genInput;
    mlTipRunner = ml.sampled.runner;

    qsStandalone = callPackage ./quickspecStandalone.nix {};

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
}
