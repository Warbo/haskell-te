{ bash, fail, haveVar, lib, makeWrapper, mkBin, runCommand, withDeps,
  writeScript }:

with lib;
with rec {
  bashEscape = mkBin {
    name   = "bashEscape";
    paths  = [ bash fail haveVar ];
    vars   = {
      sedExpr = "s/'/'\\\\''/g";
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      [[ -n "$1" ]] || fail "No name for escape value"

      TO_ESCAPE=$(cat)
      export TO_ESCAPE
      haveVar TO_ESCAPE

      # Escape ' so we can wrap values in single quotes with confidence
      ESC=$(echo "$TO_ESCAPE" | sed -e "$sedExpr")

      # Wrap in single quotes, but also surround in double quotes to bypass
      # the broken escaping of makeWrapper (it uses "foo", so by wrapping
      # our values in double quotes we get ""foo"", which is foo (our
      # single-quoted string) concatenated between two empty strings).
      echo "\"'$ESC'\""
    '';
  };

  runTest = typ: input: runCommand "check-escape-${typ}"
    {
      inherit input typ;
      buildInputs = [ bashEscape fail makeWrapper ];
      reflector = writeScript "reflector" ''
        #!/usr/bin/env bash
        set -e
        [[ -n "$X" ]] || fail "No X given"
        echo "$X"
      '';
    }
    ''
      ESC=$(echo "$input" | bashEscape typ)
      makeWrapper "$reflector" ./reflector --set X "$ESC"
      GOT=$(./reflector)

      [[ "x$GOT" = "x$input" ]] ||
        fail "Input: $input\nGot: $GOT\nEscaped: $ESC\nFile:$(cat ./reflector)"

      echo pass > "$out"
    '';

  checks = attrValues (mapAttrs runTest {
    simple  = "simple";
    spaces  = "I contain spaces";
    tick    = "I'm ticked";
    singles = "I am 'singly' quoted";
    doubles = ''I am "doubly" quoted'';
    mixture = "I'm \"mixin'\" my \"quotin'";
  });
};

withDeps checks bashEscape
