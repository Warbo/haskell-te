{ analysis, bash, fail, wrap }:

with builtins;
assert getEnv("SAMPLE") != "" ||
       abort "No SAMPLE given; ensure we're being built by quickspecTip!";

wrap {
  name   = "sampleAnalyser";
  paths  = [ analysis bash fail ];
  vars   = { SAMPLED_NAMES = getEnv("SAMPLE"); };
  script = ''
    #!/usr/bin/env bash
    set -e
    set -o pipefail

    FOUND=$(cat)

    # conjectures_for_sample expects encoded sample but decoded eqs
    RESULT=$(echo "$FOUND" | decode | conjectures_for_sample) ||
      fail "FOUND:\n$FOUND\nEND FOUND\nSAMPLED_NAMED:\n$SAMPLED_NAMES\nEND SAMPLED_NAMES"

    echo "$RESULT" | jq --slurpfile f <(echo "$FOUND") '. + {"found": $f}'
  '';
}
