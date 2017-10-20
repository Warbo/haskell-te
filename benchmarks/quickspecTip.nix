{ analysis, bash, callPackage, fail, filterToSampled, genQuickspecRunner,
  haveVar, jq, mkBin, nix, nixEnv, runCommand, testData, tipBenchmarks, tryTip,
  withDeps }:

with rec {
  quickspecTip = mkBin {
    name   = "quickspecTip";
    paths  = [
      analysis bash filterToSampled genQuickspecRunner haveVar jq nix
    ];
    vars   = rec {
      EXPR = ''
        (import ${toString ../nix-support} {}).callPackage
          ${toString ./sampleAnalyser.nix} {}
      '';
      asts    = testData.tip-benchmark.asts;
      OUT_DIR = testData.tip-benchmark.nixed;
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar SIZE
      haveVar REP

      SAMPLE=$(choose_sample "$SIZE" "$REP")
      export SAMPLE

      R=$(filterToSampled < "$asts" | genQuickspecRunner)
      A=$(nix-build --no-out-link --show-trace -E "$EXPR")

      jq -n --arg r "$R" --arg a "$A" '{"runner": $r, "analyser": $a}'
    '';
  };
};

withDeps [ (tryTip { cmd = "quickspecTip"; pkg = quickspecTip; }) ]
         quickspecTip
