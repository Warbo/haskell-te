{ mkBin, python }:

mkBin {
  name  = "renderEqs";
  paths = [ python ];
  file  = ./renderEqs.py;
}
