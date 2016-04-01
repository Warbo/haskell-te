defs: with defs;

let result      = runScript {} ''
                    "${withTime "echo" ["hello" "world"]}" > "$out"
                  '';
    jResult     = addErrorContext "Parsing as JSON:\n${result}"
                                  (fromJSON result);
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
