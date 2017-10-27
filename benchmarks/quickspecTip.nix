{ bash, fail, filterToSampled, genQuickspecRunner, runCommand, sampleAnalyser,
  testData, tipBenchmarks }:

{ rep, size }:
  with rec {
    REP        = toString rep;
    SIZE       = toString size;
    sampleFile = runCommand "sample-${SIZE}-${REP}"
      {
        inherit REP SIZE;
        buildInputs = [ tipBenchmarks.tools ];
      }
      ''
        #!/usr/bin/env bash
        set -e
        choose_sample "$SIZE" "$REP" > "$out"
      '';
  };
  {
    runner = runCommand "quickspec-tip-runner-${SIZE}-${REP}"
      {
        inherit sampleFile;
        asts        = testData.tip-benchmark.asts;
        OUT_DIR     = testData.tip-benchmark.nixed;
        buildInputs = [ filterToSampled genQuickspecRunner ];
      }
      ''
        #!/usr/bin/env bash
        set -e
        set -o pipefail
        SAMPLE=$(cat "$sampleFile")
        export SAMPLE
        R=$(filterToSampled < "$asts" | genQuickspecRunner)
        cp "$R" "$out"
      '';

    analyser = sampleAnalyser { inherit REP SIZE sampleFile; };
  }
