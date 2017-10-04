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

    runResult = result (runCmd { cmd   = "echo";
                                 args  = ["hello" "world"]; })
                        "";

    runCat = result (runCmd { cmd = "cat"; })
                    "hello world";

    checkCat = found: testFieldFile found "hello world";

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
 in {
      echo  = check runResult;
      cat   = checkCat runCat;
    }
