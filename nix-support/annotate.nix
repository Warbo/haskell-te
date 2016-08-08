{ annotateAstsScript, benchmark, explore, GetDeps, getDepsScript,
  haskellPackages, jq, parseJSON, runScript, runTypesScript, stdenv, utillinux,
  writeScript }:
{ asts, pkg, pkgSrc ? null, quick }:

with builtins;

let annotateDb = writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript { inherit pkg; pkgSrc = pkg.srcNixed; }}" |
        "${annotateAstsScript}"                                  |
        "${getDepsScript}"
    '';
    env = if haskellPackages ? pkg.name
             then { extraHs    = [ "GetDeps" pkg.name ];
                    standalone = null; }
             else { extraHs    = [ "GetDeps" ];
                    standalone = pkg.srcNixed; };
    in parseJSON (runScript { buildInputs = explore.extractedEnv (env // {
                                              f = asts;
                                            }); } ''
         set -e
         "${benchmark {
              inherit quick;
              cmd    = annotateDb;
              /*inputs = [ asts ];*/
          }}" < "${asts}" > "$out"
       '')
