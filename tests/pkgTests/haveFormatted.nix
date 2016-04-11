defs: with defs; pkg:

all [
  (testMsg (isAttrs pkg.formatted)                 "'formatted' is a set")
  (testMsg (all (x: isInt (fromJSON x)) formatted) "'formatted' keys are numeric")
  (testMsg (all isList formatted)                  "'formatted' contains lists")
  (testMsg (all (all isString) formatted)          "'formatted' lists contain strings")
]
