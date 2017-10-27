{ mkBin, python, runCommand, withDeps, wrap }:

with rec {
  inherit (builtins) toJSON;

  filterToSampled = mkBin {
    name   = "filterToSampled";
    paths  = [ python ];
    script = ''
      #!/usr/bin/env python
      import json
      import os
      import sys

      var = os.getenv('SAMPLE')
      if var.startswith('/'):
        raise Exception('SAMPLE variable "{0}" looks like a path'.format(var))
      sample = var.split('\n')

      def sampled(ast):
        """Whether the given AST is part of our chosen sample."""
        return ast['name'] in sample and ast['module' ] == 'A' \
                                     and ast['package'] == 'tip-benchmark-sig'

      def choose(ast):
        """Tells QuickSpec script to only include those ASTS we've sampled."""
        ast['quickspecable'] = ast['quickspecable'] and sampled(ast)
        return ast

      asts = json.loads(sys.stdin.read())
      print(json.dumps(map(choose, asts)))
    '';
  };

  checker = mkBin {
    name  = "checker";
    paths = [ filterToSampled python ];
    vars  = {
      SAMPLE = ''
        foo
        bar
        baz
        quux
      '';
      input = toJSON [
        {
          name          = "foo";
          module        = "B";
          package       = "tip-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "quux";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "foo";
          module        = "A";
          package       = "not-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "foo";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "bar";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = false;
        }
      ];
      output = toJSON [
        {
          name          = "foo";
          module        = "B";
          package       = "tip-benchmark-sig";
          quickspecable = false;
        }
        {
          name          = "quux";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "foo";
          module        = "A";
          package       = "not-benchmark-sig";
          quickspecable = false;
        }
        {
          name          = "foo";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = true;
        }
        {
          name          = "bar";
          module        = "A";
          package       = "tip-benchmark-sig";
          quickspecable = false;
        }
      ];
    };
    script = ''
      #!/usr/bin/env python
      from os         import getenv
      from json       import loads
      from subprocess import PIPE, Popen

      p = Popen(['filterToSampled'], stdin=PIPE, stdout=PIPE)
      (output, _) = p.communicate(getenv('input'))

      result = None
      try:
        result = loads(output)
      except:
        raise Exception(
          "Couldn't decode output:\n{0}\nEnd output".format(output))

      expect = loads(getenv('output'))
      if result != expect:
        raise Exception('Got {0}, expected {1}'.format(repr(result),
                                                       repr(expect)))

      print('pass')
    '';
  };

  check = runCommand "test-filterToSampled" { buildInputs = [ checker ]; }
                     ''checker > "$out"'';
};
withDeps [ check ] filterToSampled
