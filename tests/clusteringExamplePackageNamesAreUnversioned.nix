defs: with defs;
with builtins;

let examples = map (f: ./clusteringExamples + "/${f}")
                   (builtins.attrNames (builtins.readDir ./clusteringExamples));
    valid    = f: testMsg (parseJSON (runScript { buildInputs = [ jq ]; } ''
                 #!/usr/bin/env bash
                 set -e
                 function assertNoVersions {
                   if grep -- "-[0-9][0-9.]*$" > /dev/null
                   then
                     echo "Versions found in package names of $1${f}" 1>&2
                     exit 1
                   fi
                 }

                 echo "Checking '${f}'" 1>&2

                 echo "Parsing '${f}'" 1>&2
                 jq '.' < "${f}" > /dev/null || {
                   echo "Failed to parse '${f}'" 1>&2
                   exit 2
                 }

                 echo "Checking package names of '${f}'" 1>&2
                 jq -rc '.[] | .package'                       < "${f}" |
                   assertNoVersions ""

                 echo "Checking package names of '${f}'" 1>&2
                 jq -rc '.[] | .dependencies | .[] | .package' < "${f}" |
                   assertNoVersions "dependencies of "

                 echo "true" > "$out"
               '')) "Checking for versioned package names in '${f}'";
 in testAll (map valid examples)
