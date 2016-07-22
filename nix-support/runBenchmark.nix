{ bash, build-env, callPackage, coreutils, jq, lib, mlspec-bench, ourCheck,
  stdenv, time, writeScript }:

with builtins; with lib;

rec {

  # A quick and dirty sanity check
  knownErrors = writeScript "known-errors" ''
    jq: error
    MLSpec: Failed
    syntax error
    Argument list too long
    out of memory
  '';

  checkStderr = writeScript "check-stderr" ''
    set -e
    if grep -Ff "${knownErrors}" < "$1" 1>&2
    then
      echo "Errors found in '$1'" 1>&2
      exit 2
    fi
    exit
  '';

  # When running commands over and over to get more reliable statistics, we end
  # up with duplicate output. This script will get just the last run.
  lastEntry = writeScript "last-entry" ''
    #!/usr/bin/env bash

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

  inherit (callPackage ./timeout.nix {}) timeout;

  # A thorough benchmark, which performs multiple runs using Criterion
  withCriterion = cmd: args: trace
    "FIXME: Temporarily make withCriterion an alias for withTime, for speed"
    (writeScript "fixme" ''
      "${withTime cmd args}" | "${jq}/bin/jq" '. + {"time":{"mean":{"estPoint":1},"stddev":{"estPoint":1}}}'
    '');
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

    echo "$INPUT" | "${build-env}"   \
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

    "${checkStderr}" "$STDERR" || {
      echo "Errors found, aborting" 1>&2
      exit 3
    }

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

  # A fast benchmark, which only performs one run
  withTime = cmd: args: let shellArgs = map escapeShellArg args;
                           argStr    = concatStringsSep " " shellArgs;
    in writeScript "with-time" ''
      # Measure time with 'time', limit time/memory using 'timeout'
      "${time}/bin/time" -f '%e' -o time \
        "${timeout}" ${if trace "FIXME: re-enable benchmarking" true then "cat" else ''"${cmd}" ${argStr}''} 1> stdout 2> stderr
      CODE="$?"

      # Cache results in the store, so we make better use of the cache and avoid
      # sending huge strings into Nix
      STDOUT=$(nix-store --add stdout)
      STDERR=$(nix-store --add stderr)
        TIME=$(nix-store --add time)

      FAILED=false
      if [[ "$CODE" -ne 0 ]]
      then
        echo "Failed to time '${cmd}' with '${argStr}'" 1>&2
        echo "Contents of stderr:"                      1>&2
        cat stderr                                      1>&2
        echo "End of stderr"                            1>&2
        FAILED=true
      elif ! "${checkStderr}" "$STDERR"
      then
        echo "Errors found in '$STDERR' for '${cmd}'" 1>&2
        FAILED=true
      else
        echo "Benchmarked '${cmd}' at '$(cat time)' seconds" 1>&2
      fi

      "${jq}/bin/jq" -n --arg     time     "$(grep "^[0-9][0-9.]*$" < time)" \
                        --arg     cmd      "${cmd}"                          \
                        --argjson args     '${toJSON args}'                  \
                        --arg     stdout   "$STDOUT"                         \
                        --arg     stderr   "$STDERR"                         \
                        --arg     timefile "$TIME"                           \
                        --argjson failed   "$FAILED"                         \
                        '{"failed"   : $failed,
                          "cmd"      : $cmd,
                          "args"     : $args,
                          "stdout"   : $stdout,
                          "stderr"   : $stderr,
                          "timefile" : $timefile,
                          "time"     : {
                            "mean"   : {"estPoint": $time}}}'
    '';

  benchmark = quick: if quick then withTime else withCriterion;
}
