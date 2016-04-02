{ dumpTimesQuick, dumpTimesSlow, haskellPackages, lib }:
with lib;

let sumWithTime      = name: _: dumpTimesQuick."${name}";
    sumWithCriterion = name: _: timpTimesSlow."${name}";
in {
  totalWithTime      = mapAttrs sumWithTime      haskellPackages;
  totalWithCriterion = mapAttrs sumWithCriterion haskellPackages;
}
