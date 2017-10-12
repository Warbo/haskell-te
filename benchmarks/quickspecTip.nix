{ analysis, bash, callPackage, fail, filterToSampled, genQuickspecRunner,
  haveVar, jq, makeHaskellPkgNixable, mkBin, nix, nixEnv, runCommand, testData,
  withDeps, wrap }:

with rec {
  quickspecTip = mkBin {
    name   = "quickspecTip";
    paths  = [
      analysis bash filterToSampled genQuickspecRunner haveVar jq nix
    ];
    vars   = {
      asts    = (testData.asts         {}).teBenchmark;
      OUT_DIR = (testData.haskellNixed {}).teBenchmark;
      EXPR    = ''
        (import ${toString ../nix-support} {}).callPackage
          ${toString ./sampleAnalyser.nix} {}
      '';
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

  haveFields = runCommand "haveFields"
    (nixEnv // {
      buildInputs = [ fail jq quickspecTip ];
      SIZE     = "3";
      MAX_KB   = "1000000";
      MAX_SECS = "180";
    })
    ''
      WORKED=0
      for REP in $(seq 1 5)
      do
        export REP
             GOT=$(quickspecTip)
          RUNNER=$(echo "$GOT" | jq -r '.runner')
        ANALYSER=$(echo "$GOT" | jq -r '.analyser')
        if RESULT=$("$RUNNER" | "$ANALYSER")
        then
          WORKED=1
          break
        else
          echo "Rep '$REP' failed; hopefully just timeout or OOM, skipping" 1>&2
        fi
      done
      [[ "$WORKED" -eq 1 ]] || fail "Tried 5 reps, all failed"

      for FIELD in precision recall found wanted
      do
        echo "Checking for '$FIELD'" 1>&2
        echo "$RESULT" | jq --arg field "$FIELD" -e 'has($field)' ||
          fail "Don't have field '$FIELD':\n$RESULT\nEnd Result"
      done

      echo pass > "$out"
    '';
};

withDeps [ haveFields ] quickspecTip
