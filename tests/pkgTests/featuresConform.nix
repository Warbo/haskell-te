defs: with defs; pkg:

drvFromScript { buildInputs = [ jq ML4HSFE ]; } ''
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

  featuresConform  < "${pkg.features}"

  touch "$out"
''
