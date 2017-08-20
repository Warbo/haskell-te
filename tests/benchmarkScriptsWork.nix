defs: with defs;
with builtins;
with lib;

let result = script: input: drvFromScript {
                       inherit script input;
                       passAsFile  = [ "script" ];
                       buildInputs = explore.extractedEnv {};
                     }
                     ''
                       chmod +x "$scriptPath"
                       echo "$input" | "$scriptPath" > "$out"
                     '';

    runResult = result (runCmd  { cmd   = "echo";
                                   args  = ["hello" "world"]; })
                        "";

    runCat = result (runCmd { cmd = "cat"; })
                    "hello world";

    checkCat = found: testFieldFile found "hello world";

    testField = found: field: expect:
      testRun "Checking field ${field}" { inherit field expect; }
              { inherit expect field found; }
              ''
                echo "FOUND: $found" 1>&2
                GOT=$(jq -cr ".$field" < "$found")

                echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

                [[ "x$GOT" = "x$expect" ]] || exit 1
              '';

    testFieldFile = found: expect:
      testRun "Checking script output" null
              { inherit expect found; } ''
                F=$(cat < "$found")
                echo "F: $F" 1>&2

                GOT=$(cat "$F")
                echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

                [[ "x$GOT" = "x$expect" ]] || exit 1
              '';

    check = found: {
      stdout = testFieldFile found "hello world";
    };

    checkInput = args:
      let shouldFail = testRun "'runCmd' should abort when packages missing"
                               { inherit allArgs; }
                               { inherit dbg;
                                 buildInputs = explore.extractedEnv {}; }
                               ''
                                 if "${runCmd allArgs}" < "${inputPkgs}"
                                 then
                                   echo "'runCmd' didn't spot error" 1>&2
                                   echo "$dbg"                          1>&2
                                   exit 1
                                 fi
                               '';
          shouldSucceed = testRun "'runCmd' works when packages found"
                                  { inherit allArgs; }
                                  {
                                    inherit dbg;
                                    buildInputs = explore.extractedEnv {
                                      extraHs = [ "list-extras" "hlint" ];
                                    };
                                  }
                                  ''
                                    "${runCmd allArgs}" < "${inputPkgs}" || {
                                      echo "RunCmd didn't work" 1>&2
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

 in {
      echo  = check runResult;
      input = checkInput {};
      cat   = checkCat runCat;
    }
