{ adb-scripts, annotateAstsScript, benchmark, getDepsScript, jq, parseJSON,
  runScript, runTypesScript, writeScript }:
{ asts, pkgName, quick }:

let annotateDb = builtins.trace "FIXME: Port getDeps" writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript {}}" "${pkgName}" | "${annotateAstsScript}" | "${getDepsScript}"
    '';

 in parseJSON (runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      "${benchmark quick annotateDb []}" < "${asts}" > "$out"
    '')
