{ annotateAstsScript, benchmark, drvFromScript, explore, GetDeps, getDepsScript,
  haskellPackages, jq, parseJSON, runScript, runTypesScript, stdenv, utillinux,
  writeScript }:
{ asts, pkg, pkgSrc ? null, quick }:

with builtins;

let annotateDb = writeScript "annotateDb" ''
      #!/usr/bin/env bash

      # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

      "${runTypesScript { inherit pkg;
                          pkgSrc = if pkg ? srcNixed
                                      then pkg.srcNixed
                                      else pkgSrc; }}" |
        "${annotateAstsScript}"                                  |
        "${getDepsScript}"
    '';
    env = if haskellPackages ? pkg.name
             then { extraHs    = [ "GetDeps" pkg.name ];
                    standalone = null; }
             else { extraHs    = [ "GetDeps" ];
                    standalone = if pkg ? srcNixed
                                    then pkg.srcNixed
                                    else pkgSrc; };
    in drvFromScript {
           buildInputs = explore.extractedEnv (env // { f = asts; });
           outputs     = [ "out" "stdout" "stderr" "time" ];
           inherit asts;
         } ''
           set -e
           R=$("${benchmark {
                    inherit quick;
                    cmd    = annotateDb;
                    /*inputs = [ asts ];*/
                }}" < "$asts")

           echo "$R" > "$out"

           SO=$(echo "$R" | jq '.stdout')
           echo "$SO" "$stdout"

           SE=$(echo "$R" | jq '.stderr')
           echo "$SE" "$stderr"

           echo "$R" | jq '.time' > "$time"
       ''
