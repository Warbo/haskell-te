# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with rec {
  quickspecTip = callPackage ./quickspecTip.nix {};

  /*
  hashspecTip   = callPackage ./hashspecTip.nix   {};
  hashspecBench = callPackage ./hashspecBench.nix { inherit mlspecBench;   };
  mlspecBench   = callPackage ./mlspecBench.nix   { inherit hashspecBench; };
  hsTipSetup    = hs.sampled.genInput;
  hsTipRunner   = hs.sampled.runner;
  mlTipSetup    = ml.sampled.genInput;
  mlTipRunner   = ml.sampled.runner;
  hs = hashspecBench.benchVars;
  ml = mlspecBench.benchVars;
  */

  py = nixpkgs-2016-09.python.withPackages (p: [ p.sexpdata p.subprocess32 ]);
};

mkBin {
  name  = "python";
  paths = [ py quickspecTip tipBenchmarks.tools ];
  vars  = nixEnv // {
    NIX_EVAL_HASKELL_PKGS = ../nix-support/customHs.nix;

    parameters = toJSON {
      repetitions  = 30;
      timeout_secs = 180;
      max_size     = 20;
    };

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
