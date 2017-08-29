{ annotateScripts, bash, mkBin, runTypesScriptData }:

mkBin {
  name   = "annotateRawAstsFrom";
  paths  = [ annotateScripts.annotateScript bash ];
  vars   = { typesScript = runTypesScriptData.script; };
  script = ''
    #!/usr/bin/env bash
    pkgSrc=$(readlink -f "$1")
    export pkgSrc

    annotate
  '';
}
