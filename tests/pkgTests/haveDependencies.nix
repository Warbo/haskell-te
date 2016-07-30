defs: with defs; pkg:

testMsg (parseJSON (runScript { buildInputs = [ jq ]; } ''
                      jq 'map(has("dependencies")) | all' < "${pkg.deps}" \
                                                          > "$out"
                    ''))
        "${pkg.name} has dependencies"
