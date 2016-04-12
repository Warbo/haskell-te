defs: with defs; pkg:
with builtins;
with lib;

all id [
  (testMsg (isAttrs pkg.formatted)
           "formatted is a set")

  (testMsg (all (x: isInt (fromJSON x)) (attrNames pkg.formatted))
           "formatted keys are numeric")

  (testMsg (all (n: isList pkg.formatted.${n}) (attrNames pkg.formatted))
           "formatted contains lists")

  (testMsg (all (n: all isString pkg.formatted.${n}) (attrNames pkg.formatted))
           "formatted lists contain strings")
]
