# Scripts, mostly from tipBenchmarks, which are useful for analysing output
{ attrsToDirs, filterToSampled, genQuickspecRunner, jq, lib, runCommand,
  testData, tipBenchmarks, withDeps, wrap }:

with rec {
  scripts = attrsToDirs {
    bin = lib.genAttrs [ "choose_sample" "conjectures_for_sample" ]
                       (name: wrap {
                         inherit name;
                         file = "${tipBenchmarks.tools}/bin/${name}";
                       });
  };

  canFindComm = runCommand "can-find-commutativity"
    {
      precRec = runCommand "pr"
        {
          commEqs = runCommand "commutativityEqs.json"
            {
              commRunner = runCommand "commutativityExplorer"
                {
                  inherit (tipBenchmarks) commDeps;
                  asts        = (testData.asts         {}).teBenchmark;
                  OUT_DIR     = (testData.haskellNixed {}).teBenchmark;
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
withDeps [ canFindComm ] scripts
