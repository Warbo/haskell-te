{ buckets, buildEnv, fail, filterToSampled, genQuickspecRunner, hashspecBench,
  haskellPkgToAsts, jq, mlspecBench, nixify, quickspec, quickspecAsts,
  runCommand, stdenv, testData, tipBenchmarks, withDeps, withNix, writeScript }:

with {
  canFindComm = runCommand "can-find-commutativity"
    {
      precRec = runCommand "pr"
        {
          commEqs = runCommand "commutativityEqs.json"
            {
              commRunner = runCommand "commutativityExplorer"
                {
                  commDeps = runCommand "commDeps"
                    (tipBenchmarks.cache // {
                      getCommDeps = writeScript "getCommDeps.rkt" ''
                        #lang racket
                        (require (file "${tipBenchmarks.path}/scripts/lib/normalise.rkt"))
                        (require (file "${tipBenchmarks.path}/scripts/lib/theorems.rkt"))
                        (for ([dep (theorem-deps-of "tip2015/bin_plus_comm.smt2")])
                             (write (encode-lower-name dep)))
                      '';
                      buildInputs = [ tipBenchmarks.env ];
                    })
                    ''
                      racket "$getCommDeps" > "$out"
                    '';
                  asts        = (testData.asts {}).teBenchmark;
                  OUT_DIR     = nixify (testData.haskellPkgs {}).teBenchmark;
                  buildInputs = [ filterToSampled genQuickspecRunner jq ];
                }
                ''
                  SAMPLE=$(cat "$commDeps")
                  export SAMPLE

                  R=$(filterToSampled < "$asts" | genQuickspecRunner)
                  ln -s "$R" "$out"
                '';
            }
            ''
              "$commRunner" > "$out"
            '';
          SAMPLED_NAMES = "global746970323031352f62696e5f646973747269622e736d7432706c7573";
          buildInputs   = [ tipBenchmarks.tools ];
        }
        ''
          decode < "$commEqs" | conjectures_for_sample > "$out"
        '';
      buildInputs = [ jq ];
    }
    ''
      set -e
      jq -e '.precision | . > 0' < "$precRec"
      jq -e '.recall    | . > 0' < "$precRec"
      mkdir "$out"
    '';
};

withDeps [ canFindComm ] (buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    quickspec
    quickspecAsts
    (haskellPkgToAsts {})
    mlspecBench.mls
  ];
})
