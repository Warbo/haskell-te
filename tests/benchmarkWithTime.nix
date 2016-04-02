defs: with defs;

let result          = runScript (withNix {}) ''
                        "${withTime "echo" ["hello" "world"]}" > "$out"
                      '';
    jResult         = addErrorContext "Parsing as JSON:\n${result}"
                                      (fromJSON result);
    assertField     = field: expect:
                        let val = jResult."${field}";
                         in assertMsg (val == expect)
                                  "${field} '${val}' should be '${expect}'";
    assertFieldFile = field: expect:
                        let val = readFile (jResult."${field}");
                         in assertMsg (val == expect)
                                      "${field} '${val}' should be '${expect}'";
 in all id [
      (assertField "cmd"    "echo")
      (assertField "args"   ["hello" "world"])
      (assertFieldFile "stderr" "")
      (assertFieldFile "stdout" "hello world\n")
      (assertMsg (isString jResult.time.mean.estPoint) "Got mean time")
    ]
