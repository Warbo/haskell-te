{ annotateAstsScript, benchmark, getDeps, getDepsScript, jq, parseJSON,
  runScript, runTypesScript, stdenv, utillinux, writeScript }:
{ asts, pkg, pkgSrc ? null, quick }:

let annotateDb = writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript { inherit pkg pkgSrc; }}" |
        "${annotateAstsScript}"                   |
        "${getDepsScript}"
    '';

    in parseJSON (runScript { buildInputs = [ jq getDeps utillinux ]; } ''
         set -e
         "${benchmark quick annotateDb [] [asts]}" < "${asts}" > "$out"
       '')
