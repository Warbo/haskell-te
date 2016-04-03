defs: with defs; pkg:

parseJSON (runScript { buildInputs = [ jq ML4HSFE ]; } ''
  set -e

  function featuresConform {
    FEATURELENGTHS=$(jq -r '.[] | .features | length')
    COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
    echo "$FEATURELENGTHS" | while read -r LINE
    do
      if [[ "$LINE" -ne "$COUNT" ]]
      then
        echo "Found '$LINE' features, was expecting '$COUNT'" 1>&2
        exit 1
      fi
    done
  }

  WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${pkg.annotated}" |
    featuresConform

  echo "true" > "$out"
'')
