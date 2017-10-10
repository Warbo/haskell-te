{ buckets, buildEnv, fail, filterToSampled, genQuickspecRunner, hashspecBench,
  haskellPkgToAsts, jq, mlspecBench, nixify, quickspec, quickspecAsts,
  runCommand, stdenv, testData, tipBenchmarks, withDeps, withNix, writeScript }:

with rec {
  dep   = "global746970323031352f62696e5f646973747269622e736d7432706c7573";
  tests = rec {
    checkParamTypes = runCommand "can-find-properties-of-parameterised-types"
      (withNix {
        buildInputs  = [ fail jq tipBenchmarks.tools ];
        eqs          = testData.eqs.list-full;
        GROUND_TRUTH = ../benchmarks/ground-truth/list-full.smt2;
        TRUTH_SOURCE = ../benchmarks/ground-truth/list-full.smt2;
      })
      ''
        set -e
        set -o pipefail
        RESULT=$(echo "$eqs" | precision_recall_eqs)
        echo "$RESULT" | jq -e '.recall | . > 0' || fail "No recall"
        mkdir "$out"
      '';

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
                    asts        = testData.asts.teBenchmark;
                    OUT_DIR     = nixify testData.haskellPkgs.teBenchmark;
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
            SAMPLED_NAMES = dep;
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
};

withDeps [ tests.checkParamTypes tests.canFindComm ] (buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    quickspec
    quickspecAsts
    haskellPkgToAsts
    mlspecBench.mls
  ];
})
