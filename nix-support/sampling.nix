# Sampling from tipBenchmarks, bucketing, etc.
{}:
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
      allAnnotated  = annotated (toString tipBenchmarks.tip-benchmark-haskell);

      jqFilter      = writeScript "filter.jq" ''
        map(select(.quickspecable)) | map(select(.name as $name | $keepers | map($name == .) | any))
      '';

      filterToNames = names: runCommand "annotated-samples"
        {
          inherit allAnnotated names;
          buildInputs = [ jq ];
        }
        ''
          KEEPERS=$(jq -R '.' < "$names" | jq -s '.')
          jq --argjson keepers "$KEEPERS" -f "${jqFilter}" < "$allAnnotated" \
                                                           > "$out"
        '';
    };
    mapAttrs (_: map filterToNames) (sampleNames sizes reps);

  bucketSamples = mapAttrs (_: map (sample: {
    hashSpec = runCommand "hash-bucketed-sample"
                 {
                   inherit sample;
                   buildInputs = [ buckets.hashes ];
                 }
                 ''
                   hashBucket < "$sample" > "$out"
                 '';
    mlSpec   = error "mlSpec bucketing not implemented";
  }));
}
