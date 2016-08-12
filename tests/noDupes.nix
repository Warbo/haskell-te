defs: with defs; with builtins;

let

path  = toString ./exploreTheoriesExamples;
files = map (f: "${path}/${f}") (attrNames (readDir path));

noDupesFor = f: testRun "Testing ${f}" null { buildInputs = explore.extractedEnv {
                                                              #inherit f;
                                                            }; } ''
  set -e
  set -o pipefail

  function noDupes {
    echo "Removing dupes" 1>&2
    DUPES=$(grep "^building path.*repo-head" |
            sed -e 's/.*head-//g'            |
            sort                             |
            uniq -D) || DUPES=""
    [[ -z "$DUPES" ]] || {
      echo "Made redundant package lookups: $DUPES" 1>&2
      exit 1
    }
  }

  echo "Exploring '${f}'" 1>&2
  OUTPUT=$("${explore.explore-theories}" < "${f}" 2>&1) || {
    echo "Failed to explore '${f}'" 1>&2
    echo -e "OUTPUT:\n\n$OUTPUT\n\n" 1>&2
    exit 2
  }

  echo "$OUTPUT" | noDupes

  exit 0
'';

noDupes = map noDupesFor files;

in testWrap noDupes "No duplicate environments"
