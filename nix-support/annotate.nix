{ adb-scripts, benchmark, jq, parseJSON, runScript, withNix }:
{ asts, pkgName, quick }:

parseJSON (runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
  set -e
  "${benchmark quick "annotateDb" [pkgName]}" < "${asts}" > "$out"
'')
