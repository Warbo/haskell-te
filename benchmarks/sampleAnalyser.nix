{ analysis, bash, fail, jq, wrap }:

with builtins;
with {
  errMsg = ''
    FOUND:
      $FOUND
    END FOUND
    SAMPLED_NAMES:
      $SAMPLED_NAMES
    END SAMPLED_NAMES
  '';
};
{ REP, SIZE, SAMPLE }: wrap {
  name   = "sampleAnalyser-${SIZE}-${REP}";
  paths  = [ analysis bash fail jq ];
  vars   = { SAMPLED_NAMES = SAMPLE; };
  script = ''
    #!/usr/bin/env bash
    set -e
    set -o pipefail

    FOUND=$(cat)

    # conjectures_for_sample expects encoded sample but decoded eqs
    RESULT=$(echo "$FOUND" | decode | conjectures_for_sample) ||
      fail "${errMsg}"

    echo "$RESULT" | jq --slurpfile f <(echo "$FOUND") '. + {"found": $f}'
  '';
}
