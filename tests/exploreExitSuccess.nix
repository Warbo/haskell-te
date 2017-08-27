defs: with defs;

let

input = "${toString ./exploreTheoriesExamples}/hastily.formatted.1";

env = { buildInputs = explore.extractedEnv { f = input; } ++
                      [ explore.explore-theories ]; };

cmd = ''
  set -e

  OUTPUT=$(explore-theories "${input}" 2>&1) || {
    echo "Failed to explore 'hastily':\n$OUTPUT" 1>&2
    exit 1
  }

  touch "$out"
'';

in drvFromScript env cmd
