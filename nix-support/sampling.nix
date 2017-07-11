# Sampling from tipBenchmarks, bucketing, etc.
{ buckets, haskellPackages, jq, lib, pythonPackages, quickspecBench, runCommand,
  simpleBench, sta, tipBenchmarks, withNix, writeScript }:

with builtins;
with lib;

rec {
  # These environment variables are used by nix-eval, so we
  # can tell it where to find the benchmarks package
  env = {
    NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
    OUT_DIR = tipBenchmarks.tip-benchmark-haskell;
  } // (if getEnv "MAX_SECS" == ""
           then {}
           else { MAX_SECS = getEnv "MAX_SECS"; })
    // (if getEnv "MAX_KB" == ""
           then {}
           else { MAX_KB = getEnv "MAX_KB"; });

  qsEnv =
    with {
      extractedEnv = runCommand "quickspec-env.nix"
        (withNix (env // {
          asts = tipBenchmarks.annotatedAsts;
          buildInputs = [ (haskellPackages.ghcWithPackages
                            (h: [ h.mlspec h.nix-eval ])) ];
        }))
        ''
          # This provides an environment for running QuickSpec, without needing
          # to compile while running (which would mess up any benchmarking)
          jq 'map(select(.quickspecable))' < "$asts" |
            runhaskell "${quickspecBench.getCmd}"    |
            jq -r '.env'                             > "$out"
        '';
    };
    ((import "${extractedEnv}").override (old: {
      hsPkgs = import "${quickspecBench.augmentedHs}" {
        hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
      };
    }));

  sampleNames = size: rep:
    runCommand "sample-size-${size}-rep-${rep}"
      {
        buildInputs = [ tipBenchmarks.tools ];
      }
      ''
        choose_sample "${size}" "${rep}" > "$out"
      '';

  quickspecSample = size: rep: asts:
    with rec {
      sig = runCommand "sig-for-quickspec"
              (withNix (env // {
                inherit asts;
                buildInputs = [ (haskellPackages.ghcWithPackages
                                  (h: [ h.mlspec h.nix-eval ])) ];
              }))
              ''
                DATA=$(runhaskell "${quickspecBench.getCmd}" < "$asts")

                # Running this Haskell code (with no input) will explore the
                # functions given in our sampled ASTs
                mkdir "$out"
                echo "$DATA" | jq -r '.code' > "$out/code.hs"

                # This script will run GHC with all of the relevant options
                RUNNER=$(echo "$DATA" | jq -r '.runner')
                printf '#!/usr/bin/env bash\n%s < "%s"' "$RUNNER"      \
                                                        "$out/code.hs" \
                                                > "$out/runner.sh"
                chmod +x "$out/runner.sh"
              '';
    };
    runCommand "quickSpec-size-${size}-rep-${rep}"
      (env // {
        buildInputs = [ qsEnv ];
        inherit sig;
      })
      ''
        "${simpleBench}" "$sig/runner.sh" > "$out"
      '';

  bucketLosses = { sampleSizes, bucketSizes, reps }:
    with rec {
      data = drawSamples {
        inherit reps bucketSizes;
        sizes = sampleSizes;
      };

      iterations = { type, sampleSize, bucketSize }:
        map (iteration: iteration.buckets."${bucketSize}"."${type}".theorems.fraction)
            data."${sampleSize}";

      sampleStrs = map toString sampleSizes;

      bucketStrs = map toString bucketSizes;

      mkMean = iterations: runCommand "mean"
        {
          inherit iterations;
          buildInputs = [ jq ];
          COUNT       = toString (length iterations);
        }
        ''
          TOTAL=0
          for ITERATION in $iterations
          do
            TOTAL=$(jq --argjson t "$TOTAL" '. + $t' < "$ITERATION")
          done
          jq -n --argjson t "$TOTAL" --argjson c "$COUNT" '$t / $c' > "$out"
        '';

    };
    genAttrs [ "hashes" "recurrent" ]
      (type: genAttrs sampleStrs
               (sampleSize: genAttrs bucketStrs
                              (bucketSize: rec {
                                             fractions = iterations {
                                               inherit type sampleSize bucketSize;
                                             };
                                             mean = mkMean fractions;
                                           })));

  averageCollated = results: runCommand "time-averages"
    {
      results     = map (result: writeScript "result" (toJSON result)) results;
      buildInputs = [ jq sta ];
    }
    ''
      function stats() {
        for R in $results
        do
          jq -r '.time' < "$R"
        done | sta --q --transpose
      }

      function staToJson() {
        while read -r ENTRY
        do
          NAME=$(echo "$ENTRY" | cut -f1)
           VAL=$(echo "$ENTRY" | cut -f2)
          jq -n --arg name "$NAME" \
                --arg val  "$VAL"  \
                '{($name) : $val}'
        done |  jq -s 'reduce .[] as $x ({}; . + $x)'
      }

      stats | staToJson > "$out"
    '';

  resultsFor = args: analyseData (drawSamples args);

  analyseData = given:
    with rec {
      # Store all of the given data, to make a "checkpoint" so reproducing our
      # analysis is easier. Note this will force everything in 'given'.
      rawData = writeScript "data-for-analysis.json" (toJSON given);

      # Use data from the JSON file, to force its creation
      storedData = trace "Analysing data from ${rawData}"
                         (fromJSON (readFile "${rawData}"));
    };
    rec {
      inherit rawData;
      inherit (storedData) sizes reps bucketSizes iterations;

      # Transpose data from size[rep].system to size.system[rep]
      collatedTimes = if sizes == [] || reps == 0 then {} else
        with {
          aSample = head (head (attrValues iterations));
        };
        mapAttrs (sys: _: mapAttrs (size: map (rep: rep.outputs."${sys}"))
                                   iterations)
                 aSample.outputs;

      averageTimes = mapAttrs (sys: mapAttrs (size: averageCollated))
                              collatedTimes;
    };

  drawSamples = { sizes, reps ? 1, bucketSizes ? [] }:
    with rec {
      data = {
        inherit sizes reps bucketSizes;
        iterations = genAttrs (map toString sizes) (size:
          # One iteration for each rep; this is our raw data
          map (rep:
                with rec {
                  repS    = toString rep;
                  names   = sampleNames size repS;
                  asts    = sampleAsts names;
                  outputs = { quickSpec = quickspecSample size repS asts; };
                  buckets = bucketSample {
                    inherit asts bucketSizes possibleTheorems;
                  };
                  possibleTheorems = theoremsForNames names;
                };
                # The data above passes around lots of data using external files
                # which makes archiving and sharing data more difficult. We want
                # our output to be self-contained so we now read in those files.
                {
                  inherit rep;
                  names   = readFile names;
                  asts    = readFile asts;
                  outputs = mapAttrs (_: f:
                                       with {
                                         x = fromJSON (readFile f);
                                       };
                                       x // {
                                         stderr = readFile x.stderr;
                                         stdin  = readFile x.stdin;
                                         stdout = readFile x.stdout;
                                       })
                                     outputs;
                  buckets = trace "FIXME: Read filenames from buckets" buckets;
                  possibleTheorems = readFile possibleTheorems;
                })
              (range 1 reps));
      };

      stored = writeScript "drawn-samples.json" (toJSON data);
    };
    trace "Data saved to ${stored}" data;

  sampleAsts =
    with rec {
      jqFilter      = writeScript "filter.jq" ''
        map(select(.quickspecable)) |
        map(select(.name as $name   |
                   $keepers         |
                   map($name == .)  |
                   any))
      '';
    };
    names: runCommand "annotated-samples"
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

  theoremFraction = { found, possible }:
    runCommand "fraction"
      {
        inherit found possible;
        buildInputs = [ jq ];
      }
      ''
        L_F=$(wc -l < "$found")
        L_P=$(wc -l < "$possible")
        jq -n --argjson F "$L_F" --argjson P "$L_P" '$F / $P' > "$out"
      '';

  bucketSample = { asts, bucketSizes, possibleTheorems }:
    with rec {
      bkts  = buckets;

      mkBkt = size: rec {
        hashes = rec {
          buckets = runCommand "hash-bucketed-${toString size}"
            {
              inherit asts;
              buildInputs  = [ bkts.hashes ];
              CLUSTER_SIZE = toString size;
            }
            ''
              hashBucket < "$asts" > "$out"
            '';

          theorems = rec {
            found    = theoremsForBuckets buckets;
            fraction = theoremFraction { inherit found possibleTheorems; };
          };
        };

        recurrent = rec {
          buckets = runCommand "recurrent-bucketed-sample"
            {
              inherit asts;
              buildInputs  = [ bkts.recurrent ];
              CLUSTER_SIZE = toString size;
              OUT_DIR      = tipBenchmarks.tip-benchmark-haskell;
              # FIXME: Is OUT_DIR still needed?
            }
            ''
              recurrentBucket < "$asts" > "$out"
            '';

          theorems = rec {
            found    = theoremsForBuckets buckets;
            fraction = theoremFraction { inherit found possibleTheorems; };
          };
        };
      };
    };
    genAttrs (map toString bucketSizes) mkBkt;

  theoremsForNames = names:
    runCommand "possible-theorems"
      {
        inherit names;
        buildInputs = [ tipBenchmarks.tools ];
      }
      ''
        decode < "$names" | conjectures_admitted_by_sample > "$out"
      '';

  theoremsForBuckets = buckets:
    runCommand "bucket-theorems"
      {
        inherit buckets;
        buildInputs = [ tipBenchmarks.tools jq ];
      }
      ''
        while read -r NAMES
        do
          echo "$NAMES" | jq -r '.[]' | decode | conjectures_admitted_by_sample
        done < <(jq -c '.[] | map(.name)' < "$buckets") | grep '^.' > "$out"
      '';
}
