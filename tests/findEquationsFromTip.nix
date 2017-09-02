defs: with defs; with builtins; with lib;

with rec {
  dep = "global746970323031352f62696e5f646973747269622e736d7432706c7573";

  # *Spec should be able to find commutativity
  getCommDeps = writeScript "getCommDeps.rkt" ''
    #lang racket
    (require (file "${tipBenchmarks.path}/scripts/lib/normalise.rkt"))
    (require (file "${tipBenchmarks.path}/scripts/lib/theorems.rkt"))
    (for ([dep (theorem-deps-of "tip2015/bin_plus_comm.smt2")])
      (write (encode-lower-name dep)))
  '';

  commDeps = runCommand "commDeps"
    (tipBenchmarks.cache // {
      inherit getCommDeps;
      buildInputs = [ tipBenchmarks.env ];
    })
    ''
      racket "$getCommDeps" > "$out"
    '';

  commRunner = runCommand "commutativityExplorer"
    {
      inherit commDeps;
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

  commEqs = runCommand "commutativityEqs.json"
    {
      inherit commRunner;
    }
    ''
      "$commRunner" > "$out"
    '';

  findRep = runCommand "dep-rep"
    {
      buildInputs = [ tipBenchmarks.tools ];
      inherit dep;
    }
    ''
      echo "Looking for rep containing '$dep'" 1>&2
      for REP in $(seq 1 1000)
      do
        if choose_sample 1 "$REP" | grep "$dep" > /dev/null
        then
          echo "$REP" > "$out"
          exit 0
        fi
      done

      echo "Error: Didn't find sample containing '$dep'" 1>&2
    '';

  precRec = runCommand "pr"
    {
      inherit commEqs;
      SAMPLED_NAMES = dep;
      buildInputs   = [ tipBenchmarks.tools ];
    }
    ''
      decode < "$commEqs" | conjectures_for_sample > "$out"
    '';
};
{
  commutativity = testRun "Can find commutativity" null
    {
      inherit precRec;
      buildInputs = [ jq ];
    }
    ''
      set -e
      jq -e '.precision | . > 0' < "$precRec"
      jq -e '.recall    | . > 0' < "$precRec"
    '';

  parameterisedTypes = testRun "Can find properties of parameterised types" null
    (withNix {
      buildInputs  = [ jq package tipBenchmarks.tools ];
      eqs          = testData.eqs.list-full;
      GROUND_TRUTH = ../benchmarks/ground-truth/list-full.smt2;
      TRUTH_SOURCE = ../benchmarks/ground-truth/list-full.smt2;
    })
    ''
      set -e
      set -o pipefail

      RESULT=$(echo "$eqs" | precision_recall_eqs)

      echo "$RESULT" 1>&2

      echo "$RESULT" | jq -e '.recall | . > 0' 1>&2

      echo "pass" > "$out"
    '';
}
