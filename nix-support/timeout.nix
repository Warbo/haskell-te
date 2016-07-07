{ writeScript }:

let timeLimSecs = "3600";
    memLimKb    = "2000000";
    timeout     = writeScript "timeout"
                    (builtins.readFile "${../packages/timeout/timeout}");
 in writeScript "with-timeout" ''
      perl "${timeout}" -c --no-info-on-success -t ${timeLimSecs} -m ${memLimKb} "$@"
    ''
