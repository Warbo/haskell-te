{ time, writeScript, bash, jq, coreutils, lib, explore-theories, mlspec-bench }:

with builtins; with lib;

rec {
  lastEntry = writeScript "last-entry" ''
    #!${bash}/bin/bash

    # Get everything following last occurrence of -----
    function upToDashes {
      while read -r LINE
      do
        if [[ "x$LINE" = "x-----" ]]
        then
          break
        else
          echo "$LINE"
        fi
      done
    }

    "${coreutils}/bin/tac" "$1" | upToDashes | "${coreutils}/bin/tac"
  '';

  withCriterion = cmd: args: trace
    "FIXME: Temporarily make withCriterion an alias for withTime, for speed"
    (writeScript "fixme" ''
      "${withTime cmd args}" | "${jq}/bin/jq" '. + {"time":{"mean":{"estPoint":1},"stddev":{"estPoint":1}}}'
    '');
  # A thorough benchmark, which performs multiple runs using Criterion
  withCriterion2 = cmd: args: writeScript "with-criterion" ''
    #!${bash}/bin/bash
    set -e

    # Stop Perl (i.e. Nix) complaining about unset locale variables
    export LOCALE_ARCHIVE=/run/current-system/sw/lib/locale/locale-archive

    # Force Haskell to use UTF-8, or else we get I/O errors
    export LANG="en_US.UTF-8"

    # Check if we need to provide any input; to prevent waiting for user input
    if [ -t 0 ]
    then
        INPUT=""
    else
        INPUT=$(cat)
    fi

    # Set up environment for mlspec-bench
    mkdir -p outputs
    export BENCH_DIR="$PWD"
    export BENCHMARK_COMMAND="${cmd}"
    export BENCHMARK_ARGS='${toJSON args}'

    echo "Benchmarking '${cmd}'" 1>&2

    START_TIME="$SECONDS" # Not part of the benchmark, just info for user

    echo "$INPUT" | "${explore-theories}/bin/build-env"   \
                      "${mlspec-bench}/bin/mlspec-bench"   \
                        --template json                     \
                        --output report.json 1> bench.stdout \
                                             2> bench.stderr ||
    { echo "Benchmark exited with error" 1>&2; exit 1; }

    DURATION=$(( SECONDS - START_TIME ))
    echo "Benchmarking took '$DURATION' seconds" 1>&2

    cat bench.stdout 1>&2

    for F in stdout stderr
    do
      FOUND=0
      while read -r FILE
      do
        FOUND=1
        "${lastEntry}" "$FILE" > "./$F"
      done < <(find ./outputs -name "*.$F")
      [[ "$FOUND" -eq 1 ]] || {
        echo "Got no $F from mlspec-bench" 1>&2
        exit 1
      }
    done

    # Cache results in the store, so we make better use of the cache and avoid
    # sending huge strings into Nix
    STDOUT=$(nix-store --add stdout)
    STDERR=$(nix-store --add stderr)

    "${jq}/bin/jq" -n --arg       cmd    '${cmd}'         \
                      --argjson   args   '${toJSON args}' \
                      --arg       stdout "$STDOUT"        \
                      --arg       stderr "$STDERR"        \
                      --slurpfile report report.json      \
                      '{"cmd"    : $cmd,
                        "args"   : $args,
                        "stdout" : $stdout,
                        "stderr" : $stderr,
                        "time"   : {
                          "mean"   : ($report[0][0].reportAnalysis.anMean),
                          "stddev" : ($report[0][0].reportAnalysis.anStdDev)}}'
  '';

  # A fast benchmark, which performs one run using the 'time' command
  withTime = cmd: args: let shellArgs = map escapeShellArg args;
                            argStr    = concatStringsSep " " shellArgs;
    in writeScript "with-time" ''
      "${time}/bin/time" -f '%e' -o time "${cmd}" ${argStr} 1> stdout 2> stderr || {
        echo "Failed to time '$*'" 1>&2
        cat stderr 1>&2
        exit 1
      }

      echo "Benchmarked '${cmd}' at '$(cat time)' seconds" 1>&2

      # Cache results in the store, so we make better use of the cache and avoid
      # sending huge strings into Nix
      STDOUT=$(nix-store --add stdout)
      STDERR=$(nix-store --add stderr)

      "${jq}/bin/jq" -n --arg     time "$(cat time)"    \
                        --arg     cmd  "${cmd}"         \
                        --argjson args '${toJSON args}' \
                        --arg     stdout "$STDOUT"      \
                        --arg     stderr "$STDERR"      \
                        '{"cmd"    : $cmd,
                          "args"   : $args,
                          "stdout" : $stdout,
                          "stderr" : $stderr,
                          "time"   : {
                            "mean" : {"estPoint": $time}}}'
    '';
  benchmark = quick: if quick then withTime else withCriterion;
}
