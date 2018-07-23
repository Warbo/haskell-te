# Env vars required for using Nix commands inside builders
{ withNix }:

{
  value           = { inherit (withNix {}) NIX_REMOTE NIX_PATH; };
  removeOverrides = true;  # Since they can't be serialised into an environment
}
