defs: with defs; pkg:
with builtins;
with lib;

let

checkEqs = label: c: data: testAll (map (checkEqsFile label c) data);

checkEqsFile = label: c: data: testAll [
  (testMsg (isString data) "Data is a string ${toJSON data}")

  (testMsg (parseJSON (runScript { buildInputs = [ jq ]; } ''
    set -e
    echo "Looking for equations in ${data} (${label})" 1>&2

    [[ -e "${data}" ]] || {
      echo "No such path '${data}'" 1>&2
      exit 2
    }

    jq -s 'type == "array"' < "${data}" > "$out"
  '')) "Equations form an array")
];

result = src: label: c:
  assert isAttrs src;
  assert isString label;
  assert isInt c;
  let results = mapAttrs (checkEqs label) src;
      key     = toString c;
   in addErrorContext "result '${toJSON src}' '${label}' '${key}'"
        (testWrap [ results."${key}" ]
                 "Equations for '${pkg.name}.${label}' in '${key}' clusters");

in testAll [
     (testMsg (isAttrs pkg.explored)
              "explored isAttrs ${toJSON pkg.explored}")

     (testMsg (all (n: isList pkg.explored."${n}") (attrNames pkg.explored))
              "explored contains lists ${toJSON pkg.explored}")

     (testAll (map (result pkg.explored "explored") defaultClusters))
   ]
