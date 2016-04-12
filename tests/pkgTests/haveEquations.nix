defs: with defs; pkg:
with builtins;
with lib;

let

checkEqs = label: c: all (checkEqsFile label c);

checkEqsFile = label: c: data: all id [
  (testMsg (isString data) "Data is a string ${toJSON data}")

  (parseJSON (runScript { buildInputs = [ jq ]; } ''
    set -e
    echo "Looking for equations in ${data} (${label})" 1>&2

    [[ -e "${data}" ]] || {
      echo "No such path '${data}'" 1>&2
      exit 2
    }

    jq -s 'type == "array"' < "${data}" > "$out"
  ''))
];

result = src: label: c:
  testMsg (mapAttrs (checkEqs label) src).${toString c}
          "Equations for '${pkg.name}.${label}' in '${toString c}' clusters";

checkAll = label: src: all id [
  (testMsg (isAttrs src)
           "${label} isAttrs ${toJSON src}")

  (testMsg (all (n: isList src.${n}) (attrNames src))
           "${label} contains lists ${toJSON src}")

  (testMsg (all (result src label) defaultClusters)
           "All clusters of ${label} have equations")
];

in checkAll "explored" pkg.explored
