# A clean clone of nixpkgs, augmented with our own packages and utilities
args:

let

# We provide our own packages using the "packageOverrides" config option. This
# lets us do "deep" replacements, i.e. if we replace "foo", then anything
# depending on "foo" will use our version.

nixArgs = { config = { packageOverrides = import ./defs.nix self; }; } // args;

# Some of our scripts invoke Nix, using the usual '<nixpkgs>' path to access
# definitions. We override that path (see 'withNix') to point at this file, so
# that the same versions are used everywhere.

self = import ./nixpkgs.nix nixArgs;

in self
