{ perl, stdenv, writeScript }:

with builtins;

rec {

timeLimSecs   = 3600;

memLimKb      = 2000000;

timeoutSrc    = writeScript "timeout"
                            (builtins.readFile
                               "${../packages/timeout/timeout}");

timeoutScript = writeScript "with-timeout" ''
  perl "${timeoutSrc}" -c --no-info-on-success \
       -t ${toString timeLimSecs} -m ${toString memLimKb} "$@"
'';

timeout = stdenv.mkDerivation {
  name = "timeout";
  progagatedBuildInputs = [ perl ];
  buildCommand = ''
    source $stdenv/setup
    set -e

    mkdir -p "$out/bin"
    cp "${timeoutScript}" "$out/bin/timeout"
  '';
};

}
