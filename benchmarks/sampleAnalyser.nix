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
{ REP, SIZE, sampleFile ? null, SAMPLED_NAMES ? null}:
assert filter (x: x)
              [(sampleFile == null) (SAMPLED_NAMES == null)] == [true] ||
       (abort (toJSON {
                inherit sampleFile SAMPLED_NAMES;
                error = "Need sampleFile xor SAMPLED_NAMES";
              }));
wrap {
  name   = "sampleAnalyser-${SIZE}-${REP}";
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
