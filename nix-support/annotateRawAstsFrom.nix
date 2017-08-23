{ annotateScripts, attrsToDirs, bash, fail, runTypesScriptData, withDeps,
  wrap }:

with rec {
  annotateRawAstsFrom = attrsToDirs {
    bin = {
      annotateRawAstsFrom = wrap {
        name   = "annotateRawAstsFrom";
        paths  = [ bash fail ];
        vars   = {
          inherit (annotateScripts) annotateScript;
          typesScript = runTypesScriptData.script;
        };
        script = ''
          #!/usr/bin/env bash
          pkgSrc=$(readlink -f "$1")
          export pkgSrc

          "$annotateScript"
        '';
      };
    };
  };

  checks = [];
};

withDeps checks annotateRawAstsFrom
