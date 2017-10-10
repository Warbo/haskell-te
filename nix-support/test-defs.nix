{ callPackage, drvFromScript, lib, writeScript }:

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
}
