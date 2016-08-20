defs: with defs;
with builtins;
with lib;

let examples = mapAttrs (f: _: ./clusteringExamples + "/${f}")
                        (builtins.readDir ./clusteringExamples);

    unversioned = f: _ testMsg (parseJSON (runScript  )) ;
 in mapAttrs (_: func:
               mapAttrs (_: f: let inherit (func f) script msg env;
                                in testRun msg null env script)
                        examples) {
  valid = f: {
    msg    = "Example '${f}' is valid";
    env    = {};
    script = ''
      set -e
      jq '.' < "${f}" > /dev/null
    '';
  };

  unversioned = f: {
    msg    = "Checking for versioned package names in '${f}'";
    env    = { buildInputs = [ jq ]; };
    script = ''
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

      exit 0
    '';
  };
}
