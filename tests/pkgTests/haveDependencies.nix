defs: with defs; pkg:

parseJSON (runScript {} ''
  "${jq}/bin/jq" 'map(has("dependencies")) | all' < "${pkg.deps}" > "$out"
'')
