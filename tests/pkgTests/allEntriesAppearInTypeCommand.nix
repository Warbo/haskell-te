defs: with defs; pkg:

let rawData   = testRunTypes."${pkg.name}";
    annotated = testAnnotated."${pkg.name}";
    result    = parseJSON (runScript { buildInputs = [ adb-scripts ]; } ''
      jq -c -r '.[] | .module + "." + .name' < "${annotated}" |
      while read -r LINE
      do
        jq -r '.cmd' < "${rawData}" | grep "('$LINE)" > /dev/null || {
          echo "$LINE not in '${pkg.name}' type command" 1>&2
          exit 1
        }
      done
      echo "true" > "$out"
    '');
 in assertMsg result "All '${pkg.name}' entries appear in type command"
