{ annotateAstsScript, benchmark, explore, GetDeps, getDepsScript, jq, parseJSON,
  runScript, runTypesScript, stdenv, utillinux, writeScript }:
{ asts, pkg, pkgSrc ? null, quick }:

with builtins;

let annotateDb = writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript { inherit pkg pkgSrc; }}" |
        "${annotateAstsScript}"                   |
        "${getDepsScript}"
    '';

    in parseJSON (runScript { buildInputs = explore.extractedEnv {
                                              extraHs    = [ "GetDeps"    ];
                                              standalone = pkgSrc;
                                              f          = asts;
                                            }; } ''
         set -e
         "${benchmark {
              inherit quick;
              cmd    = annotateDb;
              /*inputs = [ asts ];*/
          }}" < "${asts}" > "$out"
       '')
