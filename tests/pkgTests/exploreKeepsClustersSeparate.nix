defs: with defs; pkg:
with builtins;
with lib;

let isNum = s: addErrorContext "Parsing '${s}' as raw JSON" (isInt (fromJSON s));
 in all id [

(testMsg (isAttrs pkg.explored) "'explored' is a set")

(testMsg (all isNum (attrNames pkg.explored)) "'explored' keys are numeric")

(testMsg (all (n: all isList pkg.explored."${n}") (attrNames pkg.explored))
         "'explored.N' is a list")

(let json = writeScript "explored-test.json" (toJSON explored);
  in (testMsg (parseJSON (runScript {} ''
       set -e
       "${jq}/bin/jq" -c '. as $x | keys[] | $x[.][]' < "${json}" |
         while read -r LINE
         do
           [[ -e "$LINE" ]] || {
             echo "Was expecting path, got '$LINE'"
             exit 2
           }
         done
     ''))
     "'explored.N[i]' are paths which exist"))

]
