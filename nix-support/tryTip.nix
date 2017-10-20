{ fail, jq, nixEnv, runCommand }:

{ cmd, pkg }:
runCommand "haveFields"
  (nixEnv // {
    inherit cmd;
    buildInputs = [ fail jq pkg ];
    SIZE     = "3";
    MAX_KB   = "1000000";
    MAX_SECS = "180";
  })
  ''
    WORKED=0
    for REP in $(seq 1 5)
    do
      export REP
      GOT=$("$cmd")
        RUNNER=$(echo "$GOT" | jq -r '.runner')
      ANALYSER=$(echo "$GOT" | jq -r '.analyser')
      if RESULT=$("$RUNNER" | "$ANALYSER")
      then
        WORKED=1
        break
      else
        echo "Rep '$REP' failed; hopefully just timeout or OOM, skipping" 1>&2
      fi
    done
    [[ "$WORKED" -eq 1 ]] || fail "Tried 5 reps, all failed"

    for FIELD in precision recall found wanted
    do
      echo "Checking for '$FIELD'" 1>&2
      echo "$RESULT" | jq --arg field "$FIELD" -e 'has($field)' ||
        fail "Don't have field '$FIELD':\n$RESULT\nEnd Result"
    done

    echo pass > "$out"
  ''
