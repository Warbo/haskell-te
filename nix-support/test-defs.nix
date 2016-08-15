{ buildEnv, callPackage, dbug, drvFromScript, file, jq, lib, parseJSON,
  runScript, stdenv, writeScript}:

with builtins;
with lib;

# Each test is a derivation, which we collect up and present for evaluation

rec {
  assertList = l: isList l || abort "Not list ${toJSON l}";

  assertTest = t: isBool t || isAttrs t || abort "Not test ${toJSON t}";

  areTests   = ts: (assertList ts && all assertTest ts) ||
                   abort "Not tests ${toJSON ts}";

  stripStr   = stringAsChars (c: if elem c (upperChars ++ lowerChars)
                                    then c
                                    else "");

  testAll = tests: assert areTests tests;
                   testWrap tests "Collected tests";

  testRec = s: if isAttrs s
                  then if s ? type && s.type == "derivation"
                          then s
                          else testAll (map (n: testWrap [(testRec s."${n}")]
                                                         "Attribute ${n}")
                                            (attrNames s))
                  else if isList s
                          then testAll (map testRec s)
                          else abort "Don't know how to test ${toJSON s}";

  # Create a new test out of other ones; this lets us assign a 'higher level'
  # meaning to some results, e.g. 'tests' might be 'foo contains x',
  # 'foo contains y', 'foo contains z', whilst 'msg' might be
  # 'foo has all required fields'
  testWrap = tests: msg:
               assert areTests tests ||
                      abort "testWrap ${toJSON { inherit tests msg; }}";
               # If there are any raw booleans in 'tests', turn them into
               # trivial derivations
               let testDrvs = map (t: if isBool t
                                         then testMsg t "Unknown test"
                                         else assert isAttrs t; t)
                                  tests;
                in testRun msg null { buildInputs = testDrvs; } ''
                     # Always pass; failure is triggered by our buildInputs
                     exit 0
                   '';

  testMsg = cond: msg:
              let info = toJSON { inherit cond msg; };
               in assert isBool   cond ||
                         abort "testMsg condition not bool ${info}";
                 assert isString msg ||
                        abort "testMsg message not string ${info}";
                 testDbg cond msg null;

  testDbg = cond: msg: dbg:
              let info = toJSON { inherit cond msg dbg; };
               in assert isBool cond ||
                         abort "testDbg condition not bool ${info}";
                  testRun msg dbg {} ''
                    exit ${if cond then "0" else "1"}
                  '';

  testRun = msg: dbg: envOverride: script:
            assert isString msg;
            assert isString script;
            assert isAttrs  envOverride;
            let info       = toJSON
                               ({ inherit msg; } // (if dbg == null
                                                        then {}
                                                        else { inherit dbg; }));
                scriptFile = writeScript "test-script" script;
                hash       = unsafeDiscardStringContext (stripStr msg);
                env        = {
                  inherit info msg scriptFile;
                  name       = "test-${hash}";
                  passAsFile = [ "info" ];
                };
                buildCommand = ''
                  echo "# $msg" >> "$out"
                  echo "true"   >> "$out"

                  if "${scriptFile}"
                  then
                    echo     "ok - $msg"
                    exit 0
                  else
                    echo "not ok - $msg"
                    cat "$infoPath" 1>&2
                    exit 1
                  fi
                '';
             in assert isString msg ||
                       abort "testRun message not string ${info}";
                drvFromScript (env // envOverride) buildCommand;

  testDrvString = expect: d: msg: testRun msg null { inherit d expect; } ''
                       O=$(cat "$d")
                       [[ "x$O" = "x$expect" ]] || exit 1
                     '';

  testFiles = fs: msg: script: testRun msg null { inherit fs script; } ''
                  for F in $fs
                  do
                    "$script" "$F" || exit 1
                  done
                  exit 0
                '';

  checkPlot = plot:
    let w      = "640";
        h      = "480";
        exists = testMsg (pathExists plot) "Checking if plot '${plot}' exists";
        dims   = testMsg
                   (parseJSON
                     (runScript { buildInputs = [ file jq ]; } ''
                       set -e
                       echo "Checking '${plot}' bigger than ${w}x${h}" 1>&2
                       GEOM=$(file "${plot}" | # filename: foo, W x H, baz
                              cut -d : -f 2  | # foo, W x H,baz
                              cut -d , -f 2  ) # W x H
                       W=$(echo "$GEOM" | cut -d x -f 1)
                       H=$(echo "$GEOM" | cut -d x -f 2)

                       echo "Checking '$W'x'$H' against '${w}'x'${h}'" 1>&2
                       jq -n --argjson width  "$W" \
                             --argjson height "$H" \
                             '$width >= ${w} and $height >= ${h}' > "$out"
                     ''))
                   "Plot dimensions sufficient (indicates GNUPlot succeeded)";
     in testWrap [
          (plot != null)
          exists
          dims
        ] "Checking plot ${toJSON plot}";

  testPackages = callPackage ./testPackages.nix {};

  # Build the contents of a Nix file, using nix-build. This lets us use Nix to
  # write our tests, whilst maintaining an eval-time/build-time separation.
  runTestInDrv = testPath: extraArgs:
    let allArgs = ["(import ./nix-support {})"] ++ extraArgs;
        argStr  = concatStringsSep " " allArgs;
     in drvFromScript { inherit testPath argStr; } ''
          cd "${./..}"
          nix-build --show-trace --no-out-link \
                    -E "import ./$testPath $argStr" || exit 1
          touch "$out"
        '';
}
