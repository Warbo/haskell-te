{ time, writeScript, bash, coreutils }:

with builtins;

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

  # A thorough benchmark, which performs multiple runs using Criterion
  withCriterion = cmd: args: writeScript "with-criterion" ''
    #!${bash}/bin/bash
    set -e

    # Check if we need to provide any input; to prevent waiting for user input
    if [ -t 0 ]
    then
        INPUT=""
    else
        INPUT=$(cat)
    fi

    mkdir -p outputs
    export BENCH_DIR="$PWD"
    export BENCHMARK_COMMAND="${cmd}"
    export BENCHMARK_ARGS='${toJSON args}'

    echo "$INPUT" | "${explore-theories}/bin/build-env"  \
                      "${mlspec-bench}/bin/mlspec-bench" \
                        --template json --output report.json

    for F in stdout stderr
    do
      [[ -f outputs/*."$F" ]] || {
        # */
        echo "Got no $F from mlspec-bench" 1>&2
        exit 1
      }
      "${lastEntry}" outputs/*."$F" > "./$F" # */
    done

    "${jq}/bin/jq" --arg       cmd    '${cmd}'         \
                   --argjson   args   '${toJSON args}' \
                   --arg       stdout "$(cat stdout)"  \
                   --arg       stderr "$(cat stderr)"  \
                   --slurpfile report report.json      \
                   '{"cmd"    : $cmd,
                     "args"   : $args,
                     "stdout" : $stdout,
                     "stderr" : $stderr,
                     "report" : ($report | flatten(1))}'
  '';

  # A faster benchmark, which performs one run using the 'time' command
  withTime = cmd: args: let shellArgs = map escapeShellArg args;
                            argStr    = concatStringsSep " " shellArgs;
    in writeScript "with-time" ''
      "${time}/bin/time" -f '%e' -o time "${cmd}" ${argStr} 1> stdout 2> stderr || {
        echo "Failed to time '$*'" 1>&2
        cat stderr 1>&2
        exit 1
      }
      "${jq}/bin/jq" -n --arg     time "$(cat time)"     \
                        --arg     cmd  "${cmd}"          \
                        --argjson args "${toJSON args}"  \
                        --arg     stdout "$(cat stdout)" \
                        --arg     stderr "$(cat stderr)" \
                        '{"time"   : $time,
                          "cmd"    : $cmd,
                          "args"   : $args,
                          "stdout" : $stdout,
                          "stderr" : $stderr,
                          "report" : [{"reportAnalysis" : {
                                         "anMean"       : {
                                           "estPoint"   : $time}}}]}'
    '';
  benchmark = quick: if quick then withTime else withCriterion;
}
