defs: with defs; pkg:

let annotated   = testAnnotated."${pkg.name}";
    checkLabels = parseJSON (runScript { buildInputs = [ adb-scripts ]; } ''
      jq -c '.[] | .package'  < "${annotated}" | while read -r LINE
      do
        [[ "x$LINE" = "x\"${pkg.name}\"" ]] || {
          echo "Unlabelled: '${pkg.name}' '$LINE'" 1>&2
          exit 1
        }
      done
      echo "true" > "$out"
    '');

 in assertMsg checkLabels "Annotated ASTs for '${pkg.name}' have package labels"
