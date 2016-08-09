{ dumpToNix, gnutar, jq, lib, parseJSON, runScript, stdenv }:
with builtins; with lib;

{ quick, src }:
  stdenv.mkDerivation {
    name     = "dumped-package";
    dumped   = dumpToNix { inherit quick; pkgDir = "${src}"; };
    outputs  = [ "failed" "cmd" "args" "stdout" "stderr" "timefile" "time" "out" ];

    buildInputs  = [ jq ];
    buildCommand = ''
      source $stdenv/setup

      jq -r '.failed'   < "$dumped" > "$failed"
      jq -r '.cmd'      < "$dumped" > "$cmd"
      jq -r '.args'     < "$dumped" > "$args"
      jq -r '.timefile' < "$dumped" > "$timefile"
      jq -r '.time'     < "$dumped" > "$time"

      SO=$(jq -r '.stdout' < "$dumped")
      cp "$SO" "$stdout"

      SE=$(jq -r '.stderr' < "$dumped")
      cp "$SE" "$stderr"

      cp "$dumped" "$out"
    '';
  }
