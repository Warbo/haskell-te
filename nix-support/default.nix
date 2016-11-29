# A stable replacement for nixpkgs so we don't need to worry about version creep
args:

# Some of our scripts invoke Nix, using the usual '<nixpkgs>' path to access
# definitions. We override that path (see 'withNix') to point at this file, so
# that the same versions are used everywhere.

import ./defs.nix (import ./nixpkgs.nix ({ config = {}; } // args))
