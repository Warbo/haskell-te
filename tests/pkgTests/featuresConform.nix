defs: with defs; pkg:

with builtins;
with lib;

drvFromScript
  {
    inherit (pkg) clustered;
    buildInputs = [ jq ML4HSFE ];
  }
  ''
    set -e

    FEATURELENGTHS=$(jq -r '.[] | .features | length' < "$clustered")
    COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
    echo "$FEATURELENGTHS" | while read -r LINE
    do
      if [[ "$LINE" -eq "$COUNT" ]]
      then
        echo "Found '$LINE' features, as expected" 1>&2
      else
        echo "Found '$LINE' features, was expecting '$COUNT'" 1>&2
        exit 1
      fi
    done

    touch "$out"
  ''
