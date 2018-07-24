{ lib, path, src }:
with rec {
  oldImport = lib.fix (self: import path {
    config = { packageOverrides = import "${src}/overlay.nix" self; };
  });

  newImport = import path { overlays = [ (import "${src}/overlay.nix") ]; };

  version = (import path {}).lib.nixpkgsVersion;
};
if builtins.compareVersions version "17.03" == -1
   then oldImport
   else newImport
