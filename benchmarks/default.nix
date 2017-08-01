# Builds the environment in which to run a benchmark
args:

with builtins;
with import ../nix-support {};
with rec {
  inherit (nix-config) attrsToDirs wrap;

  qs = quickspecBench.benchVars;

  hs = hashspecBench.benchVars;

  py = nixpkgs-2016-09.python.withPackages (p: [ p.sexpdata p.subprocess32 ]);
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

        hsTipSetup  = hs.sampled.genInput;
        hsTipRunner = hs.sampled.runner;

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
        export theoryTruths='${trace "TODO: Fix quoting in wrap" toJSON {
          list-full  = ./ground-truth/list-full.smt2;
          nat-full   = ./ground-truth/nat-full.smt2;
          nat-simple = ./ground-truth/nat-simple.smt2;
        }}'
        exec "${py}/bin/python" "$@"
      '';
    };
  };
}
