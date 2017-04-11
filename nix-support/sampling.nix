# Sampling from tipBenchmarks, bucketing, etc.
{ buckets, jq, lib, runCommand, tipBenchmarks, writeScript }:

with builtins;
with lib;

rec {
  sampleNames = sizes: reps:
    genAttrs (map toString sizes) (size:
      map (rep: runCommand "sample-size-${size}-rep-${rep}"
                  {
                    buildInputs = [ tipBenchmarks.tools ];
                  }
                  ''
                    choose_sample "${size}" "${rep}" > "$out"
                  '')
          (map toString (range 1 reps)));

  drawSamples = sizes: reps:
    with rec {
      jqFilter      = writeScript "filter.jq" ''
        map(select(.quickspecable)) |
        map(select(.name as $name   |
                   $keepers         |
                   map($name == .)  |
                   any))
      '';

      filterToNames = names:
        {
          inherit names;
          asts = runCommand "annotated-samples"
            {
              inherit names;
              inherit (tipBenchmarks) annotatedAsts;
              buildInputs = [ jq ];
            }
            ''
              KEEPERS=$(jq -R '.' < "$names" | jq -s '.')
              jq --argjson keepers "$KEEPERS" \
                 -f "${jqFilter}"             < "$annotatedAsts" > "$out"
            '';
        };
    };
    bucketSamples (mapAttrs (_: map filterToNames) (sampleNames sizes reps));

  bucketSamples = mapAttrs (_: map (sample: sample // {
    hashSpec = runCommand "hash-bucketed-sample"
                 {
                   inherit (sample) asts;
                   buildInputs = [ buckets.hashes ];
                 }
                 ''
                   hashBucket < "$asts" > "$out"
                 '';
    mlSpec   = error "mlSpec bucketing not implemented";
  }));
}
