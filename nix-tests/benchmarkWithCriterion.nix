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
      (assertMsg (jResult ? report) "Got report")
      (assertMsg (isString (head jResult.report).reportAnalysis.anMean.estPoint)
                 "Report has mean time")
    ]
