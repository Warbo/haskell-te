defs: with defs;

let

input = "${toString ./exploreTheoriesExamples}/hastily.formatted.1";

env = {};

cmd = ''
  set -e

  OUTPUT=$("${explore.explore-theories}" "${input}" 2>&1) || {
    echo "Failed to explore 'hastily':\n$OUTPUT" 1>&2
    exit 1
  }

  echo "true" > "$out"
'';

in parseJSON (runScript env cmd)
