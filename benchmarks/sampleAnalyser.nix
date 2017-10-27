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
{ REP, SIZE, sampleFile }: wrap {
  name   = "sampleAnalyser-${SIZE}-${REP}";
  paths  = [ analysis bash fail jq ];
  vars   = { inherit sampleFile; };
  script = ''
    #!/usr/bin/env bash
    set -e
    set -o pipefail

    SAMPLED_NAMES=$(cat "$sampleFile")
    export SAMPLED_NAMES

    FOUND=$(cat)

    # conjectures_for_sample expects encoded sample but decoded eqs
    RESULT=$(echo "$FOUND" | decode | conjectures_for_sample) ||
      fail "${errMsg}"

    echo "$RESULT" | jq --slurpfile f <(echo "$FOUND") '. + {"found": $f}'
  '';
}
