defs: with defs;

let result = runScript { buildInputs = [ adb-scripts ]; } ''
        INPUT1='[{"name": "n1", "module": "M1"}, {"name": "n2", "module": "M2"}]'
        INPUT2='[{"name": "n2", "module": "M2", "foo": "bar"}]'
        RESULT=$(echo "$INPUT1" | tagAsts <(echo "$INPUT2") "{}")
        echo "$RESULT" | jq 'type' > "$out"
      '';
    jResult = fromJSON result;
 in assertMsg (jResult == "array") "Expected 'array', got '${jResult}'"
