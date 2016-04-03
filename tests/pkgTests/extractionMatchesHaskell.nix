defs: with defs; pkg:

# extractFeatures is written in bash + jq, and is really slow. We've
# replaced it with ml4hsfe-loop, but keep it around for testing
parseJSON (runScript { buildInputs = [ jq ML4HSFE ]; } ''
  set -e
  BASH_RESULT=$("${recurrent-clustering}/lib/extractFeatures" < "${pkg.annotated}" | jq '.') || {
    echo "Couldn't extract features with bash: $BASH_RESULT" 1>&2
    exit 2
  }

  HASKELL_RESULT=$(WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${pkg.annotated}" | jq '.') || {
    echo "Couldn't extract features with haskell: $HASKELL_RESULT" 1>&2
    exit 3
  }

  jq -n --argfile bash    <(echo "$BASH_RESULT")    \
        --argfile haskell <(echo "$HASKELL_RESULT") \
        '$bash == $haskell' > "$out"
'')
