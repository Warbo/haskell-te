defs: with defs;
with builtins;
with lib;

let examples = mapAttrs (f: _: ./clusteringExamples + "/${f}")
                        (builtins.readDir ./clusteringExamples);

    unversioned = f: _ testMsg (parseJSON (runScript  )) ;
 in mapAttrs (_: func:
               mapAttrs (f: _: let inherit (func f) script msg env;
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

  haveFeatures = f: {
    msg    = "Checking for features in '${f}'";
    env    = { buildInputs = [ ML4HSFE ]; };
    script = ''
      set -e
      O=$(WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${f}" |
            grep -c "^")

      [[ "$O" -gt 0 ]] && exit 0

      echo -e "f: ${f}\nO: $O" 1>&2
      exit 1
    '';
  };

  conform = f: {
    msg    = "Example ${f} conforms";
    env    = { buildInputs = [ ML4HSFE ]; };
    script = ''
      set -e
      function featuresConform {
        FEATURELENGTHS=$(jq -r '.[] | .features | length')
        COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
        echo "$FEATURELENGTHS" | while read -r LINE
        do
          if [[ "$LINE" -ne "$COUNT" ]]
          then
            echo "Found '$LINE' features instead of '$COUNT'" 1>&2
            exit 1
          fi
        done
      }

      WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${f}" | featuresConform
      exit 0
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
