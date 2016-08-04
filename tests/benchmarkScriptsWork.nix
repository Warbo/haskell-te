defs: with defs;
with builtins;
with lib;

let result = script: parseJSON (runScript {
                                  inherit script;
                                  passAsFile  = [ "script" ];
                                  buildInputs = explore.extractedEnv {};
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

    check = found: {
      cmd    = testField     found "cmd"    "echo";
      args   = testField     found "args"   ["hello" "world"];
      stderr = testFieldFile found "stderr" "";
      stdout = testFieldFile found "stdout" "hello world\n";

      time   = testMsg (isString found.time.mean.estPoint) "Got mean time";
    };

    checkInput = args:
      let shouldFail = testRun "'benchmark' should abort when packages missing"
                               { inherit allArgs; }
                               { inherit dbg;
                                 buildInputs = explore.extractedEnv {}; }
                               ''
                                 if "${benchmark allArgs}" < "${inputPkgs}"
                                 then
                                   echo "'benchmark' didn't spot error" 1>&2
                                   echo "$dbg"                          1>&2
                                   exit 1
                                 fi
                                 touch "$out"
                               '';
          shouldSucceed = testRun "'benchmark' works when packages found"
                                  { inherit allArgs; }
                                  {
                                    inherit dbg;
                                    buildInputs = explore.extractedEnv {
                                      extraHs = [ "list-extras" "hlint" ];
                                    };
                                  }
                                  ''
                                    "${benchmark allArgs}" < "${inputPkgs}" || {
                                      echo "Benchmark didn't work" 1>&2
                                      echo "$dbg"                  1>&2
                                      exit 1
                                    }
                                  '';
          # Haskell packages which don't appear in our scripts' dependencies
          inputPkgs = writeScript "inputs" ''
                        list-extras
                        hlint
                      '';
          allArgs = args // {
            cmd    = "true";
            inputs = [ inputPkgs ];
          };
          dbg     = toJSON { inherit allArgs; };
       in { inherit shouldFail shouldSucceed; };

    hasStdDev = testMsg (isString criterionResult.time.stddev.estPoint)
                        "Criterion gives standard deviation";

 in testRec {
  inherit hasStdDev;

  quick = {
    echo  = check timeResult;
    input = checkInput { quick = true; };
  };
  slow  = {
    echo  = check criterionResult;
    input = checkInput { quick = false; };
  };
}
