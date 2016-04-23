defs: with defs;

parseJSON (runScript {} ''
  set -e

  function explore {
    "${explore.explore-theories}" < "$1" 2>&1
  }

  explore "${toString ./exploreTheoriesExamples}/hastily.formatted.1" > /dev/null || {
    echo "Failed to explore 'hastily':\n$OUTPUT" 1>&2
    exit 1
  }

  echo "true" > "$out"
'')
