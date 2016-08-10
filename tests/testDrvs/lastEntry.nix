defs: with defs;
with builtins;

testRun "Checking lastEntry"
        null
        {}
        ''
          echo -e 'foo\n-----\nbar\n-----\nbaz' > input
          O=$("${lastEntry}" input)
          [[ "x$O" = "xbaz" ]] && exit 0

          echo "Got '$O'" 1>&2
          exit 1
        ''
