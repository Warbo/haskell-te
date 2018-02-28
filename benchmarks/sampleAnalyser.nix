{ analysis, bash, fail, jq, wrap }:

{ REP, SIZE, sampleFile ? null, SAMPLED_NAMES ? null}:

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

  err = error: abort (toJSON { inherit error sampleFile SAMPLED_NAMES; });
};

assert sampleFile == null -> SAMPLED_NAMES != null ||
       err "sampleAnalyser needs either sampleFile xor SAMPLED_NAMES";

assert sampleFile != null -> SAMPLED_NAMES == null ||
       err "sampleAnalyser can't use sampleFIle AND SAMPLED_NAMES";

assert SAMPLED_NAMES != null -> isString SAMPLED_NAMES ||
       err "SAMPLED_NAMES should be a newline-delimited string";

wrap {
  name   = "sampleAnalyser-${toString SIZE}-${toString REP}";
  paths  = [ analysis bash fail jq ];
  vars   = if sampleFile == null
              then { inherit SAMPLED_NAMES; }
              else { inherit sampleFile;    };
  script = ''
    #!/usr/bin/env bash
    set -e
    set -o pipefail

    [[ -n "$SAMPLED_NAMES" ]] || SAMPLED_NAMES=$(cat "$sampleFile")
    export SAMPLED_NAMES

    FOUND=$(cat)

    # conjectures_for_sample expects encoded sample but decoded eqs
    RESULT=$(echo "$FOUND" | decode | conjectures_for_sample) ||
      fail "${errMsg}"

    echo "$RESULT" | jq --slurpfile f <(echo "$FOUND") '. + {"found": $f}'
  '';
}
