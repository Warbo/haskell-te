defs: with defs; pkg:
with builtins;
with lib;

let isNum = s: addErrorContext "Parsing '${s}' as raw JSON" (isInt (fromJSON s));
 in {

isSet = testDbg (isAttrs pkg.explored) "'explored' is a set" pkg.explored;

numericKeys = testDbg (all isNum (attrNames pkg.explored))
                      "'explored' keys are numeric"
                      pkg.explored;

hasPaths = let typ = x: isString x || (isAttrs x && x ? type && x.type == "derivation");
            in testDbg (all (n: all typ pkg.explored."${n}") (attrNames pkg.explored))
                   "'explored.N' contains derivations"
                   pkg.explored;

pathsExist =
  let json = writeScript "explored-test.json" (toJSON pkg.explored);
   in drvFromScript { buildInputs = [ jq ]; } ''
        set -e
        jq -cr '. as $x | keys[] | $x[.][]' < "${json}" |
          while read -r LINE
          do
            [[ -e "$LINE" ]] || {
              echo "Was expecting path, got '$LINE'"
              exit 2
            }
          done
        touch "$out"
      '';

}
