defs: with defs;

with { f = "${toString ./exploreTheoriesExamples}/hastily.formatted.1"; };
runCommand "exploreExitSuccess"
  {
    inherit f;
    buildInputs = explore.extractedEnv { inherit f; } ++
                  [ explore.explore-theories ];
  }
  ''
    set -e

    OUTPUT=$(explore-theories "$f" 2>&1) || {
      echo -e "Failed to explore 'hastily' ($OUTPUT)" 1>&2
      exit 1
    }

    mkdir "$out"
  ''
