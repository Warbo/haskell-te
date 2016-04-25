{ adb-scripts, benchmark, jq, parseJSON, runScript }:
{ asts, pkgName, quick }:

parseJSON (runScript { buildInputs = [ adb-scripts ]; } ''
  set -e
  "${benchmark quick "annotateDb" [pkgName]}" < "${asts}" > "$out"
'')
