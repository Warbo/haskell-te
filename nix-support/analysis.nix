# Scripts, mostly from tipBenchmarks, which are useful for analysing output
{ attrsToDirs, fail, filterToSampled, genQuickspecRunner, jq, lib, runCommand,
  testData, tipBenchmarks, withDeps, wrap }:

with rec {
  scripts = attrsToDirs {
    bin = lib.genAttrs [ "choose_sample" "decode" "conjectures_for_sample" ]
                       (name: wrap {
                         inherit name;
                         file = "${tipBenchmarks.tools}/bin/${name}";
                       }) // {
      conjectures_for_sample = wrap {
        name = "conjectures_for_sample";
        paths  = [ tipBenchmarks.tools ];
        script = ''
          #!/usr/bin/env bash
          decode | conjectures_for_sample
        '';
      };
    };
  };

  canFindComm = runCommand "can-find-commutativity"
    {
      inherit (tipBenchmarks) commDeps;
      buildInputs   = [ fail filterToSampled genQuickspecRunner jq scripts ];
      asts          = (testData.asts         {}).test-theory;
      OUT_DIR       = (testData.haskellNixed {}).test-theory;
      SAMPLED_NAMES = "global746970323031352f62696e5f646973747269622e736d7432706c7573";
    }
    ''
      set -e
      SAMPLE=$(cat "$commDeps")
      export SAMPLE

      FLT=$(filterToSampled < "$asts")            || fail "Couldn't filter"
      RUN=$(echo "$FLT" | genQuickspecRunner)     || fail "Couldn't gen runner"
      EQS=$("$RUN")                               || fail "Couldn't gen eqs"
      CON=$(echo "$EQS" | conjectures_for_sample) || fail "Couldn't look up eqs"
      echo "$CON" | jq -e '.precision | . > 0'    || fail "No/zero precision"
      echo "$CON" | jq -e '.recall    | . > 0'    || fail "No/zero recall"
      mkdir "$out"
    '';
};
withDeps [ canFindComm ] scripts
