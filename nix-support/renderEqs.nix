{ mkBin, python, runCommand, withDeps }:

with rec {
  untested = mkBin {
    name  = "renderEqs";
    paths = [ python ];
    file  = ./renderEqs.py;
  };

  app = lhs: rhs: { inherit lhs rhs; role = "application"; };

  var = id: bound: { inherit bound id; role = "variable"; type = "unknown"; };

  con = symbol: { inherit symbol; role = "constant"; type = "unknown"; };

  example = [
    { relation = "~=";
      rhs      = var 1 false;
      lhs      = app (app (con "global64")
                          (app (app (con "global65")
                                    { role = "lambda";
                                      arg  = null;
                                      body = var 0 true; })
                               (con "Global6c")))
                     (var 1 false); }
    { relation = "~=";
      rhs      = var 0 false;
      lhs      = app (app (con "global64")
                          (app (app (con "global65")
                                    { role = "lambda";
                                      arg  = null;
                                      body = var 0 true; })
                               (con "Global6c")))
                     (var 0 false); }
  ];

  test = runCommand "render-eqs-test"
    {
      buildInputs = [ untested ];
      example     = builtins.toJSON example;
    }
    ''
      set -e
      OUTPUT=$(echo "$example" | renderEqs)
      for PAT in '~=' 'global64' 'global65' 'Global6c' 'v0' 'v1' 'λ'
      do
        echo "$OUTPUT" | grep "$PAT" > /dev/null ||
          fail "'$PAT' didn't match\n$OUTPUT"
      done
      mkdir "$out"
    '';
};
withDeps [ test ] untested
