defs: with defs;

parseJSON (runScript {} ''
  set -e

  function explore {
    "${explore.explore-theories}" < "$1" 2>&1
  }

  function noDupes {
    DUPES=$(grep "^building path.*repo-head" |
            sed -e 's/.*head-//g'            |
            sort                             |
            uniq -D)
    [[ -z "$DUPES" ]] || {
      echo "Made redundant package lookups: $DUPES" 1>&2
      exit 1
    }
  }

  echo "Making sure packages aren't checked over and over" 1>&2
  for F in "${toString ./exploreTheoriesExamples}/"*
  do
    echo "Exploring '$F'" 1>&2
    OUTPUT=$(explore "$F") || {
      echo "Failed to explore '$F'" 1>&2
      exit 2
    }
    echo "$OUTPUT" | noDupes
  done
  echo "No duplicate checks were spotted" 1>&2
  echo "true" > "$out"
'')
