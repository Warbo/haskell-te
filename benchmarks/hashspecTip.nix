{ mkBin, tryTip, withDeps }:

with rec {
  hashspecTip = mkBin {
    name = "hashspecTip";
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

withDeps [ (tryTip { cmd = "hashspecTip"; pkg = hashspecTip; }) ]
         hashspecTip
