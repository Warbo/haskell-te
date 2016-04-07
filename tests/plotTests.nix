defs: with defs;
with lib;
with plots;

testMsg (all id [
  (checkPlot plotEqsVsTimeForKs)
]) "Checking final plots"
