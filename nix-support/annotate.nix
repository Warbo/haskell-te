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

    getResult = writeScript "get-annotatedb-result" ''
                  #!/usr/bin/env bash
                  set -e
                  BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
                  cat "$BASE/result.json"
                '';

    getStdout = writeScript "get-annotatedb-stdout" ''
                  #!/usr/bin/env bash
                  set -e
                  STDOUT=$(getBenchmarkResult | "${jq}/bin/jq" -r '.stdout')
                  cat "$STDOUT"
                '';

 in stdenv.mkDerivation {
      name         = "annotatedb";
      buildInputs  = [ asts jq getDeps utillinux ];
      buildCommand = ''
        source $stdenv/setup

        set -e
        mkdir "$out"
        getBenchmarkStdout | "${benchmark quick annotateDb []}" > "$out/result.json"

        cp "${getResult}" "$out/bin/getBenchmarkResult"
        cp "${getStdout}" "$out/bin/getBenchmarkStdout"
      '';
    }
