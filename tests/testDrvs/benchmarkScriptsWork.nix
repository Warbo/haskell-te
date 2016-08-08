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
      testRun "Checking field ${field}" { inherit field expect; }
              { inherit expect field found; }
              ''
                echo "FOUND: $found" 1>&2
                GOT=$(jq -cr ".$field" < "$found")

                echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

                [[ "x$GOT" = "x$expect" ]] || exit 1
              '';

    testFieldFile = found: field: expect:
      testRun "Checking field file ${field}" null
              { inherit expect field found; } ''
                F=$(jq -r ".$field" < "$found")
                echo "F: $F" 1>&2

                GOT=$(cat "$F")
                echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

                [[ "x$GOT" = "x$expect" ]] || exit 1
              '';


    check = found: {
      cmd    = testField     found "cmd"    "echo";
      args   = testField     found "args"   ''["hello","world"]'';
      stderr = testFieldFile found "stderr" "";
      stdout = testFieldFile found "stdout" "hello world";

      time   = testRun "Got mean time" null { inherit found; } ''
                 echo "Looking for mean time in $found" 1>&2
                 T=$(jq -r '.time.mean.estPoint | type' < "$found")
                 echo "Got '$T'" 1>&2
                 [[ "x$T" = "xstring" ]] && exit 0
                 [[ "x$T" = "xnumber" ]] && exit 0
                 exit 1
               '';
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
