defs: with defs;

let

input = "${toString ./exploreTheoriesExamples}/hastily.formatted.1";

env = { buildInputs = explore.extractedEnv null input; };

cmd = ''
  set -e

  OUTPUT=$("${explore.explore-theories input}" "${input}" 2>&1) || {
    echo "Failed to explore 'hastily':\n$OUTPUT" 1>&2
    exit 1
  }

  touch "$out"
'';

in drvFromScript env cmd
