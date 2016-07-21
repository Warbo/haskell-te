defs: with defs; pkg:
with builtins;
with lib;

let

check = data:
  let stdout = runScript { buildInputs = [ jq ]; } ''
                 set -e
                 jq 'map(.quickspecable) | all' < "${data}" > "$out"
               '';
      result = if stdout == ""
                  then trace "Got empty output" false
                  else parseJSON stdout;
   in testMsg result "Ensuring all quickspecable ${toJSON data}";

checkAll = mapAttrs (c: fmt: testWrap (map check fmt)
                                      "Checking ${c} quickspecable")
                    pkg.formatted;

in testWrap (map (c: checkAll."${toString c}") defaultClusters)
            "Only 'quickspecable' definitions get formatted for ${pkg.name}"
