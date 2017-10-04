defs: with defs;
with builtins;
with lib;
with {
  testOutput = { given, input }:
    testRun "Checking script output" null
      {
        inherit input;
        expect      = "hello world";
        script      = runCmd given;
        passAsFile  = [ "script" ];
      }
      ''
        chmod +x "$scriptPath"
        GOT=$(echo "$input" | "$scriptPath")

        echo -e "GOT: $GOT\nEXPECT: $expect" 1>&2

        [[ "x$GOT" = "x$expect" ]] || exit 1
      '';
};
mapAttrs (_: testOutput) {
  echo = { given = { cmd = "echo"; args = ["hello" "world"]; }; input = ""; };
  cat  = { given = { cmd = "cat"; }; input = "hello world"; };
}
