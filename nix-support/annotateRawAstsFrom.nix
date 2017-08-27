{ annotateScripts, bash, fail, mkBin, runTypesScriptData }:

mkBin {
  name   = "annotateRawAstsFrom";
  paths  = [ annotateScripts.annotateScript bash fail ];
  vars   = {
    typesScript = runTypesScriptData.script;
  };
  script = ''
    #!/usr/bin/env bash
    pkgSrc=$(readlink -f "$1")
    export pkgSrc

    annotate
  '';
}
