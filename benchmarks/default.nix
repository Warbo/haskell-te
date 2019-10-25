# Builds the environment in which to run a benchmark
args:

with builtins;
with import ./.. {};
with lib;
with rec {
  noCompiling = writeScript "noCompilingDuringBenchmarking.nix" ''
    with builtins; abort "Tried to build Nix env during a benchmark"
  '';

  parameters = {
    max_size      = 20;

    # NOTE: These numbers are one-less-than their corresponding samples, e.g.
    # a specific rep '20' will run 'choose_sample SIZE 21'
    repetitions   = 1;       # Repeat this many times unless specific_reps given
    specific_reps = [ 30 ];  # Use instead of range(0, repetitions) unless empty

    timeout_secs  = 300;
  };

  # NOTE: For historical reasons (implicit list indices), the "rep" parameter
  # given to "choose_sample" is 1+ the index we use here (hence "repMinusOne")
  samples =
    listToAttrs
      (map (size: {
             name  = toString size;
             value = listToAttrs
                       (map (repMinusOne: {
                              name  = toString repMinusOne;
                              value = quickspecTip {
                                inherit size;
                                # For historical consistency, choose_sample is
                                # run with 1+ the JSON key
                                rep = repMinusOne + 1;
                              };
                            })
                            # These are the numbers which appear in the JSON
                            (if parameters.specific_reps == []
                                then range 0 (parameters.repetitions - 1)
                                else parameters.specific_reps));
           })
           (range 1 parameters.max_size));

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
    #!${bash}/bin/bash
    exec python "$@"
  '';
}
