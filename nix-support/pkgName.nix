{ lib, reverse }:
with builtins;
with lib;
with rec {
  # Technically allows things like '.....' as numbers, but meh
  isDigit = x: any (n: n == x) (stringToCharacters "0123456789.");

  numeric = x: all isDigit (stringToCharacters x);

  stripNums = xs: if xs == []
                     then []
                     else if numeric (head xs)
                             then stripNums (tail xs)
                             else xs;

  stripEndNums = xs: reverse (stripNums (reverse xs));

  stripVersion = s: concatStringsSep "-" (stripEndNums (splitString "-" s));
};

stripVersion
