{ bash, callPackage, coreutils, explore, jq, lib, mlspec-bench, ourCheck,
  runScript, stdenv, strip, time, writeScript }:

with builtins; with lib;

rec {

  # A quick and dirty sanity check
  knownErrors = writeScript "known-errors" ''
    jq: error
    MLSpec: Failed
    syntax error
    Argument list too long
    out of memory
    ^error:
  '';

  checkStderr = writeScript "check-stderr" ''
    set -e
    if grep -f "${knownErrors}" < "$1" 1>&2
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

  # Check that the required Haskell packages are found in the environment
  checkHsEnv = extra:
    let allGiven = extra ++ explore.extra-haskell-packages;
     in writeScript "checkHsEnv" ''
          #!/usr/bin/env bash
          set -e
          set -o pipefail

          function ensurePkg {
            # Skip empty lines
            echo "$1" | grep '[a-zA-Z_]' > /dev/null || return 0

            if ghc-pkg list "$1" | grep "$1" > /dev/null
            then
              return 0
            fi

            echo "Aborting. Didn't find Haskell package '$1' in" 1>&2
            ghc-pkg list 1>&2
            exit 1
          }

          # We must have ghc-pkg, or else we can't even check the others
          command -v "ghc-pkg" > /dev/null 2>&1 || {
            echo "No ghc-pkg command in environment" 1>&2
            exit 1
          }

          # '|| true' to appease 'set -e' when we have no input
          INPUT=""
          [ -t 0 ] || INPUT=$(sort -u | grep "^.") || true

          if [[ -n "$INPUT" ]]
          then
            echo "Checking for extra packages: $INPUT" 1>&2
            while read -r PKG
            do
              ensurePkg "$PKG"
            done < <(echo "$INPUT" | grep '[a-zA-Z_]' | "${explore.findHsPkgReferences}")
          fi

          while read -r PKG
          do
            ensurePkg "$PKG"
          done < <(echo "${concatStringsSep "\n" allGiven}")

          exit 0
        '';

  # Snippets of code which are common to both withTime and withCriterion

  checkEnv = inputs:
    let pkgNames      = map strip maybePkgNames;
        maybePkgNames = if inputs == [] then []
                                        else splitString "\n" (runScript {} ''
          cat ${concatStringsSep " " (map (x: "'${x}'") inputs)} |
            grep '[a-zA-Z_]'                                     |
            "${explore.findHsPkgReferences}" > "$out"
        '');
     in ''
          echo "$INPUT" | "${checkHsEnv []}" || {
            echo "checkHsEnv failed" 1>&2
            exit 1
          }
        '';

  cacheOutputs = ''
    # Cache results in the store, so we make better use of the cache and avoid
    # sending huge strings into Nix
    STDOUT=$(nix-store --add stdout)
    STDERR=$(nix-store --add stderr)
  '';

  checkResult = { cmd, args, stdout, stderr, time }: ''
    if [[ "$CODE" -ne 0 ]]
    then
      echo "Failed to time '${cmd}' with '${args}'" 1>&2

      echo "Contents of stderr:" 1>&2
      cat  ${stderr}             1>&2 || true
      echo "End of stderr"       1>&2

      echo "Contents of stdout:" 1>&2
      cat  ${stdout}             1>&2 || true
      echo "End of stdout"       1>&2

      FAILED=true
    elif ! "${checkStderr}" "$STDERR"
    then
      echo "Errors found in '$STDERR' for '${cmd}'" 1>&2
      FAILED=true
    else
      DURATION=$(cat "${time}")
      echo "Benchmarked '${cmd}', took:" 1>&2
      cat "${time}"                      1>&2
    fi
  '';

  mkReport = { cmd, args, inFields, outFields }: ''
    "${jq}/bin/jq" -n ${inFields} --arg     cmd    '${cmd}'         \
                                  --argjson args   '${toJSON args}' \
                                  --arg     stdout "$STDOUT"        \
                                  --arg     stderr "$STDERR"        \
                                  --argjson failed "$FAILED"        \
                      '{"failed"   : $failed,
                        "cmd"      : $cmd,
                        "args"     : $args,
                        "stdout"   : $stdout,
                        "stderr"   : $stderr,
                        ${outFields} }'
  '';

  # A thorough benchmark, which performs multiple runs using Criterion
  withCriterion = { quick, cmd, args ? [], inputs ? []}:
    writeScript "with-criterion" ''
      #!${bash}/bin/bash
      set -e

      INPUT=$(cat)
      ${checkEnv inputs}

      echo "Setting up environment for mlspec-bench" 1>&2

      # Stop Perl (i.e. Nix) complaining about unset locale variables
      export LOCALE_ARCHIVE=/run/current-system/sw/lib/locale/locale-archive

      # Force Haskell to use UTF-8, or else we get I/O errors
      export LANG="en_US.UTF-8"

      mkdir -p outputs
      export BENCH_DIR="$PWD"
      export BENCHMARK_COMMAND="${cmd}"
      export BENCHMARK_ARGS='${toJSON args}'

      echo "$INPUT" | "${mlspec-bench}/bin/mlspec-bench"     \
                        --template json                      \
                        --output report.json 1> bench.stdout \
                                             2> bench.stderr ||
      CODE="$?"

      FAILED=false
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
          FAILED=true
        }
      done

      ${cacheOutputs}

      TIME=$(nix-store --add report.json)

      ${checkResult {
          inherit cmd;
          args   = toJSON args;
          stdout = "bench.stdout";
          stderr = "bench.stderr";
          time   = "$TIME";
      }}

      ${mkReport {
          inherit cmd args;
          inFields = ''
            --slurpfile report report.json \
          '';
          outFields = ''
            "time" : {"mean"   : ($report[0][0].reportAnalysis.anMean),
                      "stddev" : ($report[0][0].reportAnalysis.anStdDev)}
          '';
      }}
    '';

  # A fast benchmark, which only performs one run
  withTime = { quick, cmd, args ? [], inputs ? []}:
   let shellArgs = map escapeShellArg args;
       argStr    = concatStringsSep " " shellArgs;
    in writeScript "with-time" ''
         INPUT=$(cat)
         ${checkEnv inputs}

         # Measure time with 'time'
         echo "$INPUT" |
           "${time}/bin/time" -f '%e' -o time \
             "${cmd}" ${argStr} 1> stdout 2> stderr
         CODE="$?"

         ${cacheOutputs}

         TIME=$(nix-store --add time)

         FAILED=false
         ${checkResult {
             inherit cmd;
             args   = argStr;
             stdout = "stdout";
             stderr = "stderr";
             time   = "time";
         }}

         ${mkReport {
             inherit cmd args;
             inFields = ''
               --arg time     "$(grep "^[0-9][0-9.]*$" < time)" \
               --arg timefile "$TIME"                           \
             '';
             outFields = ''
               "timefile" : $timefile,
               "time"     : {"mean" : {"estPoint" : $time}}
             '';
         }}
       '';

  benchmark = args: (if args.quick then withTime else withCriterion) args;
}
