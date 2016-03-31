{ lib, annotate, dumpedPackages }:

with lib;

mapAttrs (flip annotate) dumpedPackages
