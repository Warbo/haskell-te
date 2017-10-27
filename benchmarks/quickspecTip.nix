{ analysis, bash, callPackage, fail, filterToSampled, genQuickspecRunner,
  haveVar, jq, mkBin, nix, nixEnv, runCommand, sampleAnalyser, testData,
  tipBenchmarks, tryTip, withDeps }:

{ rep, size }:
  with rec {
    REP    = toString rep;
    SIZE   = toString size;
    SAMPLE = runCommand "sample-${SIZE}-${REP}"
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
        inherit SAMPLE;
      }
      ''
        #!/usr/bin/env bash
        set -e
        set -o pipefail
        filterToSampled < "$asts" | genQuickspecRunner > "$out"
      '';

    analyser = sampleAnalyser { inherit SAMPLE; };
  }
