defs: with defs; with builtins; with lib;
{}
/*FIXME: Don't use sampling
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
    (tipBenchmarks.cache // { buildInputs = [ tipBenchmarks.env ]; })
    ''
      racket "${getCommDeps}" > "$out"
    '';

  commDepAsts = sampling.sampleAsts commDeps;

  commEqs     = sampling.quickspecSample "none" "none" commDepAsts;

  commEqsJson = runCommand "comm-deps-eq-count"
    {
      inherit commEqs;
      buildInputs = [ jq package ];
    }
    ''
      quickspec
      F=$(jq -r '.stdout' < "$commEqs")
      grep '^{' < "$F" | jq -s '.' > "$out"
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
      inherit commEqsJson;
      SAMPLED_NAMES = dep;
      buildInputs   = [ tipBenchmarks.tools ];
    }
    ''
      decode < "$commEqsJson" | conjectures_for_sample > "$out"
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
      buildInputs  = [ jq tipBenchmarks.tools ];

      NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
      GROUND_TRUTH          = ../benchmarks/ground-truth/list-full.smt2;
      TRUTH_SOURCE          = ../benchmarks/ground-truth/list-full.smt2;

      SETUP = runCommand "setup.json"
        (withNix {
          inherit (quickspecBench.benchVars.standalone)
            genAnnotatedPkg genInput;

          buildInputs = [ jq ];
          theory      = ../benchmarks/list-full.smt2;

          NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
        })
        ''
          set -e

          DATA=$("$genAnnotatedPkg" < "$theory")

          ANNOTATED=$(echo "$DATA" | jq -r '.annotated')
            OUT_DIR=$(echo "$DATA" | jq -r '.out_dir'  )

          export OUT_DIR

          "$genInput" < "$ANNOTATED" |
            jq --arg dir "$OUT_DIR" '. + {"out_dir": $dir}' > "$out"
        '';
    })
    ''
      set -e

       RUNNER=$(jq -r '.runner'  < "$SETUP")
         CODE=$(jq -r '.code'    < "$SETUP")
          ENV=$(jq -r '.env'     < "$SETUP")
      OUT_DIR=$(jq -r '.out_dir' < "$SETUP")

      export OUT_DIR

      EQS=$(echo "$CODE" | nix-shell -p "$ENV" --run "$RUNNER" |
            grep -v '^Depth')

      echo "$EQS" 1>&2

      RESULT=$(echo "$EQS" | jq -s '.' | precision_recall_eqs)

      echo "$RESULT" 1>&2

      echo "$RESULT" | jq -e '.recall | . > 0' 1>&2

      echo "pass" > "$out"
    '';
}
*/
