defs: with defs;
with builtins;

let result = runScript { buildInputs = [ GetDeps ]; } ''
        INPUT1='[{"name": "n1", "module": "M1"}, {"name": "n2", "module": "M2"}]'
        INPUT2='[{"name": "n2", "module": "M2", "foo": "bar"}]'
        RESULT=$(echo "$INPUT1" | "${tagAstsScript}" <(echo "$INPUT2") "{}")
        echo "$RESULT" | jq 'type' > "$out"
      '';
    jResult = fromJSON result;
 in testMsg (jResult == "array") "Expected 'array', got '${jResult}'"
