defs: with defs;
with builtins;
with lib;
with {
  testFieldFile = { given, input }:
    testRun "Checking script output" null
      {
        expect = "hello world";
        found  = drvFromScript
          {
            inherit input;
            script      = runCmd given;
            passAsFile  = [ "script" ];
          }
          ''
            chmod +x "$scriptPath"
            echo "$input" | "$scriptPath" > "$out"
          '';
      }
      ''
        F=$(cat < "$found")
        echo "F: $F" 1>&2

        GOT=$(cat "$F")
        echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

        [[ "x$GOT" = "x$expect" ]] || exit 1
      '';
};
mapAttrs (_: testFieldFile) {
  echo = { given = { cmd = "echo"; args = ["hello" "world"]; }; input = ""; };
  cat  = { given = { cmd = "cat"; }; input = "hello world"; };
}
