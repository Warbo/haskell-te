defs: with defs; pkg: with pkg;

let rawData   = testRunTypes."${name}";
    result    = parseJSON (runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      jq -c -r '.[] | .module + "." + .name' < "${annotated}" |
      while read -r LINE
      do
        jq -r '.cmd' < "${rawData}" | grep "('$LINE)" > /dev/null || {
          echo "$LINE not in '${name}' type command" 1>&2
          exit 1
        }
      done
      echo "true" > "$out"
    '');
 in assertMsg result "All '${name}' entries appear in type command"
