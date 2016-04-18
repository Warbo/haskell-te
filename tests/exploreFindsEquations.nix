defs: with defs;

let path   = toString ./exploreTheoriesExamples;
    result = runScript {} ''
  set -e

  function explore {
    "${explore.explore-theories}" < "$1" 2>&1
  }

  echo "Making sure exploration actually works" 1>&2
  FOUND=0
  for F in "${path}/"*
  do
    echo "Exploring '$F'" 1>&2
    OUTPUT=$(explore "$F") || {
      echo "Failed to explore '$F': $OUTPUT" 1>&2
      exit 2
    }

    if echo "$OUTPUT" | grep "No clusters found"
    then
      echo "No clusters found by MLSpec (did it receive any input?)" 1>&2
      exit 3
    fi

    if echo "$OUTPUT" | grep "^{" > /dev/null
    then
      echo "Found equations for '$F'" 1>&2
      FOUND=1
    else
      echo -e "Couldn't find any equations in output of '$F':\n$OUTPUT" 1>&2
    fi
  done

  if [[ "$FOUND" -eq 0 ]]
  then
    echo "No equations found from files in ${path}/" 1>&2
    exit 4
  fi

  echo "Exploration worked, found some equations from data/" 1>&2
  echo "true" > "$out"
'';

in testMsg (parseJSON result) "Equations found"
