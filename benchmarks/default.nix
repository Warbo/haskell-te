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
      vars = {
        qsSetup  = qs.sampled.genInput;
        qsRunner = qs.sampled.runner;
      };
      file = "${python}/bin/python";
    };
  };
}
