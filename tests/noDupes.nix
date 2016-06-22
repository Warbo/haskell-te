defs: with defs; with builtins;

let

path   = toString ./exploreTheoriesExamples;

files  = map (f: "${path}/f") (attrNames (readDir path));

noDupesFor = f: parseJSON (runScript {} ''
  set -e
  set -o pipefail

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

  echo "Exploring '${f}'" 1>&2
  OUTPUT=$("${explore.explore-theories f}" < "${f}" 2>&1) || {
    echo "Failed to explore '${f}'" 1>&2
    exit 2
  }

  echo "$OUTPUT" | noDupes

  echo "true" > "$out"
'');

noDupes = all noDupesFor files;

in testMsg noDupes "No duplicate environments"
