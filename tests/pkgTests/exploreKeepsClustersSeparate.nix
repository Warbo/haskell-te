defs: with defs; pkg:
with builtins;
with lib;

let isNum = s: addErrorContext "Parsing '${s}' as raw JSON" (isInt (fromJSON s));
 in testAll [

(testMsg (isAttrs pkg.explored) "'explored' is a set ${toJSON pkg.explored}")

(testMsg (all isNum (attrNames pkg.explored))
         "'explored' keys are numeric ${toJSON pkg.explored}")

(testMsg (all (n: all isString pkg.explored."${n}") (attrNames pkg.explored))
         "'explored.N' contains paths ${toJSON pkg.explored}")

(let json = writeScript "explored-test.json" (toJSON pkg.explored);
  in (testMsg (parseJSON (runScript {} ''
       set -e
       "${jq}/bin/jq" -cr '. as $x | keys[] | $x[.][]' < "${json}" |
         while read -r LINE
         do
           [[ -e "$LINE" ]] || {
             echo "Was expecting path, got '$LINE'"
             exit 2
           }
         done
       echo "true" > "$out"
     ''))
     "'explored.N[i]' are paths which exist ${toJSON pkg.explored}"))

]
