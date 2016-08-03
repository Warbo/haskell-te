defs: with defs; pkg:
with builtins;
with lib;

let

checkEqs = label: c: data: testWrap (map (checkEqsFile label c) data)
                                    "Check eqs for ${label} ${toString c}";

checkEqsFile = label: c: data: testWrap [
  (testDbg (isString data) "Data is a string" { inherit data; })

  (testMsg (parseJSON (runScript { buildInputs = [ jq ]; } ''
    set -e
    echo "Looking for equations in ${data} (${label})" 1>&2

    [[ -e "${data}" ]] || {
      echo "No such path '${data}'" 1>&2
      exit 2
    }

    jq -s 'type == "array"' < "${data}" > "$out"
  '')) "Equations form an array")
] "Check eqs file for ${label} ${toString c}";

result = src: label: c:
  assert isAttrs src;
  assert isString label;
  assert isInt c;
  let results = mapAttrs (checkEqs label) src;
      key     = toString c;
   in addErrorContext "result '${toJSON src}' '${label}' '${key}'"
        (testWrap [ results."${key}" ]
                 "Equations for '${pkg.name}.${label}' in '${key}' clusters");

in {
  isAttrs      = testDbg (isAttrs pkg.explored)
                         "explored isAttrs"
                         { inherit (pkg) explored; };

  haveLists    = testDbg (all (n: isList pkg.explored."${n}")
                              (attrNames pkg.explored))
                         "explored contains lists"
                         { inherit (pkg) explored; };

  gotEquations = listToAttrs (map (c: {
                                    name  = toString c;
                                    value = result pkg.explored "explored" c;
                                  })
                                  defaultClusters);
}
