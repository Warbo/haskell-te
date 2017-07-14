# Builds the environment in which to run a benchmark
args:

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
        qsTipSetup  = qs.sampled.genInput;
        qsTipRunner = qs.sampled.runner;

        qsStandaloneMkPkg  = qs.standalone.genAnnotatedPkg;
        qsStandaloneSetup  = qs.standalone.genInput;
        qsStandaloneRunner = qs.standalone.runner;

        theoryFiles = builtins.toJSON {
          list-full  = ./list-full.smt2;
          nat-full   = ./nat-full.smt2;
          nat-simple = ./nat-simple.smt2;
        };
      };
      file = "${python}/bin/python";
    };
  };
}
