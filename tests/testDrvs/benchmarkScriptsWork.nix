defs: with defs;
with builtins;
with lib;

let result = script: drvFromScript {
                       inherit script;
                       passAsFile  = [ "script" ];
                       buildInputs = explore.extractedEnv {};
                     }
                     ''
                       chmod +x "$scriptPath"
                       "$scriptPath" > "$out"
                     '';

    timeResult      = result (withTime      { quick = true;
                                              cmd   = "echo";
                                              args  = ["hello" "world"]; });
    criterionResult = result (withCriterion { quick = false;
                                              cmd   = "echo";
                                              args  = ["hello" "world"]; });

    testField = found: field: expect:
      let val = found."${field}";
        #x = testMsg (val == expect)
        #          "${field} '${toJSON val}' should be '${toJSON expect}'";
       in           testRun "Checking field ${field}" { inherit field expect; }
                          { inherit found; }
                          ''
                            echo "FOUND: $found"
                            exit 1
                          '';

    testFieldFile = found: field: expect:
      let x=1;#val = readFile (found."${field}");
       in #testMsg (val == expect)
          #          "${field} '${toJSON val}' should be '${toJSON expect}'";
          testRun "Checking field file ${field}" null
                  { inherit found; } ''
                    echo "TFF: $found" 1>&2
                    exit 1
                  '';


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

    hasStdDev = testRun "Criterion gives standard deviation" null
                        { inherit criterionResult; } ''
                          T=$(jq -r '.time.stddev.estPoint | type' < "$criterionResult")
                          [[ "x$T" = "xnumber" ]] || exit 1
                        '';

 in {
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
