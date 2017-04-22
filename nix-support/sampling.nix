# Sampling from tipBenchmarks, bucketing, etc.
{ buckets, haskellPackages, jq, lib, pythonPackages, quickspecBench, runCommand,
  simpleBench, sta, tipBenchmarks, withNix, writeScript }:

with builtins;
with lib;

rec {
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

      /*
      mcNemar = { possible, foundA, foundB }:
        runCommand "mcnemar"
        {
          inherit possible foundA foundB;
          buildInputs = [ pythonPackages.statsmodels pythonPackages.python ];
          tester = writeScript "mcnemar.py" ''
            #!/usr/bin/env python
            import os
            import numpy                                as np
            import statsmodels.stats.contingency_tables as ctables

            env   = os.environ
            table = np.asarray([[env['A'], env['B']],
                                [env['C'], env['D']]])

            print repr(ctables.mcnemar(table, exact=True))
          '';
        }
        ''
          A=0  # Both found
          B=0  # A found, not B
          C=0  # B found, not A
          D=0  # Neither found

          while read -r THM
          do
            GOTA=N
            GOTB=N

            if grep -Fx "$THM" < "$foundA" > /dev/null
            then
              GOTA=Y
            fi

            if grep -Fx "$THM" < "$foundB" > /dev/null
            then
              GOTB=Y
            fi

            case "$GOTA$GOTB" in
              YY)
                A=$(( A + 1 ))
                ;;
              YN)
                B=$(( B + 1 ))
                ;;
              NY)
                C=$(( C + 1 ))
                ;;
              NN)
                D=$(( D + 1 ))
                ;;
              *)
                echo "Error: Unexpected table entry: '$GOTA' '$GOTB'" 1>&2
                exit 1
                ;;
            esac

          done < "$possible"

          export A B C D
          "$tester"
        '';
        */

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

  sampleTimes = mapAttrs (_: reps: with rec {
                             names = attrNames (head reps).runtimes;
                           };
                           genAttrs names
                                    (name: map (rep: rep.runtimes."${name}")
                                               reps));

  averageTimes = samples:
    mapAttrs (size: mapAttrs (type: results:
                                runCommand "averages-${size}-${type}"
                                  {
                                    inherit results;
                                    buildInputs = [ jq sta ];
                                  }
                                  ''
                                    function times() {
                                      for R in $results
                                      do
                                        jq -r '.time' < "$R"
                                      done
                                    }

                                    function collect() {
                                      jq -s 'reduce .[] as $x ({}; . + $x)'
                                    }

                                    times                 |
                                      sta --q --transpose |
                                      while read -r ENTRY
                                      do
                                        NAME=$(echo "$ENTRY" | cut -f1)
                                         VAL=$(echo "$ENTRY" | cut -f2)
                                        jq -n --arg name "$NAME" \
                                              --arg val  "$VAL"  \
                                              '{($name) : $val}'
                                      done | collect > "$out"
                                  ''))
             (sampleTimes samples);

  drawSamples = { sizes, reps ? 1, bucketSizes ? [] }:
    genAttrs (map toString sizes) (size:
      map (rep: rec {
            runtimes = {
              quickSpec = with rec {
                # These environment variables are used by nix-eval, so we
                # can tell it where to find the benchmarks package
                env = {
                  NIX_EVAL_HASKELL_PKGS = quickspecBench.customHs;
                  OUT_DIR = tipBenchmarks.tip-benchmark-haskell;
                };

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

                    # This provides an environment for running the above
                    echo "$DATA" | jq -r '.env' > "$out/env.nix"
                  '';
              };
              runCommand "quickSpec-size-${size}-rep-${rep}"
                (env // {
                  buildInputs = [
                    ((import "${sig}/env.nix").override (old: {
                        hsPkgs = import "${quickspecBench.augmentedHs}" {
                          hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
                        };
                    }))
                  ];
                  inherit sig;
                })
                ''
                  "${simpleBench}" "$sig/runner.sh" > "$out"
                '';
            };

            names    = runCommand "sample-size-${size}-rep-${rep}"
                         {
                           buildInputs = [ tipBenchmarks.tools ];
                         }
                         ''
                           choose_sample "${size}" "${rep}" > "$out"
                         '';

            asts     = sampleAsts names;

            buckets  = bucketSample {
              inherit asts bucketSizes;
              inherit (theorems) possible;
            };

            theorems = { possible = theoremsForNames names; };
          })
          (map toString (range 1 reps)));

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

  bucketSample = { asts, bucketSizes, possible }:
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
            fraction = theoremFraction { inherit found possible; };
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
            fraction = theoremFraction { inherit found possible; };
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
