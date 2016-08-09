{ dumpToNix, downloadToNix, drvFromScript, parseJSON }:
{ quick, pkgName}:

with builtins;

let dump = dumpToNix { inherit quick; pkgDir = downloadToNix pkgName; };
 in drvFromScript {
      inherit dump;
      outputs = [ "out" "stdout" "stderr" "time" "args" "cmd" "failed" ];
    } ''
        SE=$(jq -r '.stderr' < "$dump")
        cp "$SE" "$stderr"

        SO=$(jq -r '.stdout' < "$dump")
        cp "$SO" "$stdout"

        jq -r '.time'   < "$dump" > "$time"
        jq -r '.args'   < "$dump" > "$args"
        jq -r '.cmd'    < "$dump" > "$cmd"
        jq -r '.failed' < "$dump" > "$failed"

        cp "$dump" "$out"
      ''
