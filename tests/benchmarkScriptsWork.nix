defs: with defs;
with builtins;
with lib;

let result = script: parseJSON (runScript {
                                  inherit script;
                                  passAsFile = [ "script" ];
                                }
                                ''
                                  chmod +x "$scriptPath"
                                  "$scriptPath" > "$out"
                                '');

    timeResult      = result (withTime      { quick = true;
                                              cmd   = "echo";
                                              args  = ["hello" "world"]; });
    criterionResult = result (withCriterion { quick = false;
                                              cmd   = "echo";
                                              args  = ["hello" "world"]; });

    testField = found: field: expect:
      let val = found."${field}";
       in testMsg (val == expect)
                  "${field} '${toJSON val}' should be '${toJSON expect}'";

    testFieldFile = found: field: expect:
      let val = readFile (found."${field}");
       in testMsg (val == expect)
                    "${field} '${toJSON val}' should be '${toJSON expect}'";

    check = found: testAll [
              (testField     found "cmd"                         "echo")
              (testField     found "args"                        ["hello" "world"])
              (testFieldFile found "stderr"                      "")
              (testFieldFile found "stdout"                      "hello world\n")
              (testMsg       (isString found.time.mean.estPoint) "Got mean time")
            ];

    hasStdDev = testMsg (isString criterionResult.time.stddev.estPoint)
                        "Criterion gives standard deviation";

 in testAll [(check timeResult) (check criterionResult) hasStdDev]
