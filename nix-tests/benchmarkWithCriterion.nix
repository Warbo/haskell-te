defs: with defs;

let result      = runScript (withNix {}) ''
                    "${withCriterion "echo" ["hello" "world"]}" > "$out"
                  '';
    jResult     = parseJSON result;
    assertField = field: expect:
                    let val = jResult."${field}";
                     in assertMsg (val == expect)
                                  "${field} '${val}' should be '${expect}'";
 in all id [
      (assertField "stderr" "")
      (assertField "stdout" "hello world")
      (assertField "cmd"    "echo")
      (assertField "args"   ["hello" "world"])
      (assertMsg (isString jResult.time.mean.estPoint)   "Got mean time")
      (assertMsg (isString jResult.time.stddev.estPoint) "Got stddev")
    ]
