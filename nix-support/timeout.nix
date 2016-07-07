{ writeScript }:

with builtins;

rec {

timeLimSecs   = 3600;

memLimKb      = 2000000;

timeoutScript = writeScript "timeout"
                            (builtins.readFile
                               "${../packages/timeout/timeout}");

timeout       = writeScript "with-timeout" ''
  perl "${timeoutScript}" -c --no-info-on-success \
       -t ${toString timeLimSecs} -m ${toString memLimKb} "$@"
'';

}
