defs: with defs;

drvFromScript { buildInputs = explore.exploreEnv; } ''
  set -e
  set -x

  "${checkHsEnv [                                    ]}" || exit 1
  "${checkHsEnv ["text"                              ]}" || exit 2
  "${checkHsEnv ["text" "containers"                 ]}" || exit 3
  "${checkHsEnv ["text" "containers" "parsec"        ]}" || exit 4
  "${checkHsEnv ["text" "containers" "parsec" "aeson"]}" || exit 5

  touch "$out"
''
