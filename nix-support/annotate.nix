{ annotateAstsScript, benchmark, explore, GetDeps, getDepsScript, jq, parseJSON,
  runScript, runTypesScript, stdenv, utillinux, writeScript }:
{ asts, pkg, pkgSrc ? null, quick }:

with builtins;

let pkgSrcNixed = if pathExists (unsafeDiscardStringContext
                       "${toString standalone}/default.nix")
                     then pkgSrc
                     else nixedHsPkg "${pkgSrc}" null;
    annotateDb = writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript { inherit pkg pkgSrcNixed; }}" |
        "${annotateAstsScript}"                   |
        "${getDepsScript}"
    '';

    in parseJSON (runScript { buildInputs = explore.extractedEnv {
                                              extraHs    = [ "GetDeps"    ];
                                              standalone = pkgSrcNixed;
                                              f          = asts;
                                            }; } ''
         set -e
         "${benchmark {
              inherit quick;
              cmd    = annotateDb;
              /*inputs = [ asts ];*/
          }}" < "${asts}" > "$out"
       '')
