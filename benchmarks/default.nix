# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with lib;
with rec {
  noCompiling = writeScript "noCompilingDuringBenchmarking.nix" ''
    with builtins; abort "Tried to build Nix env during a benchmark"
  '';

  parameters = {
    repetitions  = 30;
    timeout_secs = 300;
    max_size     = 19;
  };

                                   (range 1 parameters.repetitions))
  samples = map (size: map (rep: quickspecTip { inherit rep size; })
                (range 1 parameters.max_size);

  py             = nixpkgs-2016-09.python.withPackages
                     (p: [ p.sexpdata p.subprocess32 ]);
  quickspecTip   = callPackage ./quickspecTip.nix   { inherit sampleAnalyser; };
  sampleAnalyser = callPackage ./sampleAnalyser.nix {};

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
};

mkBin {
  name  = "python";
  paths = [ py tipBenchmarks.tools ];
  vars  = nixEnv // {
    HASKELL_PACKAGES      = noCompiling;
    NIX_EVAL_HASKELL_PKGS = noCompiling;

    parameters   = toJSON parameters;

    qsStandalone = callPackage ./quickspecStandalone.nix {};

    quickspecTip = runCommand "qstip.json"
      {
        buildInputs = [ fail ];
        passAsFile  = [ "content" ];
        content     = toJSON samples;
      }
      ''
        set -e
        [[ -f "$contentPath" ]] || fail "No path '$contentPath'"
        cp "$contentPath" "$out"
      '';

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
