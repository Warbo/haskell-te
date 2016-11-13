{ annotateAstsScript, benchmark, drvFromScript, explore, getDepsScript,
  haskellPackages, runTypesScript, stdParts, storeParts, writeScript }:

with builtins;

{ asts, pkg, pkgSrc ? null, quick }:

let
  annotateDb = writeScript "annotateDb" ''
    #!/usr/bin/env bash

    # Turns output from dump-package or dump-hackage into a form suitable for ML4HS.

    "${runTypesScript { inherit pkg;
                        pkgSrc = if pkg ? srcNixed
                                    then pkg.srcNixed
                                    else pkgSrc; }}" |
      "${annotateAstsScript}"                        |
      "${getDepsScript}"
  '';

  env = if haskellPackages ? pkg.name
                 then { extraHs    = [ "GetDeps" pkg.name ];
                        standalone = null; }
                 else { extraHs    = [ "GetDeps" ];
                        standalone = if pkg ? srcNixed
                                        then pkg.srcNixed
                                        else pkgSrc; };

in drvFromScript
     {
       buildInputs = explore.extractedEnv (env // { f = asts; });
       outputs     = stdParts;
       inherit asts;
     }
     ''
       set -e
       O=$("${benchmark {
                inherit quick;
                cmd = annotateDb;
            }}" < "$asts")

       ${storeParts}
     ''
