{ haskellPackages, lib }:
with lib;
let totalWithTime      = name: _: ...;
    totalWithCriterion = name: _: ...;
in {
  totalWithTime      = mapAttrs sumWithTime haskellPackages;
  totalWithCriterion = mapAttrs sumWithCriterion haskellPackages;
}
