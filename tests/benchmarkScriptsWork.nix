defs: with defs;

let result = script: parseJSON (runScript (withNix {}) ''
                        "${script}" > "$out"
                     '');

    timeResult      = result (withTime      "echo" ["hello" "world"]);
    criterionResult = result (withCriterion "echo" ["hello" "world"]);

    assertField     = found: field: expect:
      let val = found."${field}";
       in assertMsg (val == expect)
                    "${field} '${toJSON val}' should be '${toJSON expect}'";

    assertFieldFile = found: field: expect:
      let val = readFile (found."${field}");
       in assertMsg (val == expect)
                    "${field} '${toJSON val}' should be '${toJSON expect}'";

    check = found: all id [
              (assertField         found    "cmd"    "echo")
              (assertField         found    "args"   ["hello" "world"])
              (assertFieldFile     found "stderr" "")
              (assertFieldFile     found "stdout" "hello world\n")
              (assertMsg (isString found.time.mean.estPoint)   "Got mean time")
            ];

    hasStdDev = assertMsg (isString criterionResult.time.stddev.estPoint)
                          "Criterion gives standard deviation";

 in check timeResult && check criterionResult && hasStdDev
