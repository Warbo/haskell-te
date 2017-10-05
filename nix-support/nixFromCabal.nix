{ lib, nixedHsPkg }:
with builtins; with lib;

# Make a Nix package definition from a Cabal project. The result is a function,
# accepting its dependencies as named arguments, returning a derivation. This
# allows mechanisms like "haskellPackages.callPackage" to select the appropriate
# dependencies for this version of GHC, etc.

# "dir" is the path to the Cabal project (this could be checked out via fetchgit
# or similar)

# f is a function for transforming the resulting derivation, e.g. it might
# override some aspects. If "f" is "null", we use the package as-is. Otherwise,
# we perform a tricky piece of indirection which essentially composes "f" with
# the package definition, but also preserves all of the named arguments required
# for "haskellPackages.callPackage" to work.

dir: f:
  with rec {
    result = import (toString (nixedHsPkg dir));

    # Support an "inner-composition" of "f" and "result", which behaves like
    # "args: f (result args)" but has explicit named arguments, to allow
    # "functionArgs" to work (as used by "callPackage").
    # TODO: Hopefully Nix will get a feature to set a function's argument names
    # Build a string "a,b,c" for the arguments of "result" which don't have
    # defaults
    resultArgs = functionArgs result;
    required   = filter (n: !(getAttr n resultArgs)) (attrNames resultArgs);
    arglist    = concatStringsSep "," required;

    # Strip the dependencies off our strings, so they can be embedded
    arglistF   = unsafeDiscardStringContext arglist;

    # Write a special-purpose composition function to a file, accepting the same
    # arguments ("arglistF") as "result".
    compose = toFile "cabal-compose.nix" ''
      f: g: args@{${arglistF}}: f (g args)
    '';
  };

  # If we've been given a function "f", compose it with "result" using our
  # special-purpose function
  assert f == null || isFunction f ||
         abort "nixFromCabal: f should be null or function, given ${typeOf f}";

  if f == null then result
               else import compose f result
