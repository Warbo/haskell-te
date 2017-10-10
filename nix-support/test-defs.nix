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
