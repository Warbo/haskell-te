# Env vars required for using Nix commands inside builders. Note that
# 'callPackage' will pollute the result, so use 'import'.
{ withNix }:

{ inherit (withNix {}) NIX_REMOTE NIX_PATH; }
