{ callPackage, drvFromScript, lib, writeScript }:

with builtins;
with lib;

# Each test is a derivation, which we collect up and present for evaluation

rec {
  assertList = l: isList l || abort "Not list ${toJSON l}";

  assertTest = t: isBool t || isAttrs t || abort "Not test ${toJSON t}";

  areTests   = ts: (assertList ts && all assertTest ts) ||
                   abort "Not tests ${toJSON ts}";

  stripStr   = stringAsChars (c: if elem c (upperChars ++ lowerChars)
                                    then c
                                    else "");
}
