{ drvFromScript, haskellPackages, lib, stdenv }:
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

rec {

nixedHsPkg = dir: f:

  assert typeOf dir == "path" || isString dir;
  assert f == null || isFunction f;

  let hsVer   = haskellPackages.ghc.version;

      # Find the .cabal file and read properties from it
      cabalF  = head (filter (x: hasSuffix ".cabal" x) (attrNames (readDir dir)));
      cabalC  = map (replaceStrings [" " "\t"] ["" ""])
                    (splitString "\n" (readFile (dir + "/${cabalF}")));

      getField = f: replaceStrings [f (toLower f)] ["" ""]
                                   (head (filter (l: hasPrefix          f  l ||
                                                     hasPrefix (toLower f) l)
                                                 cabalC));

      pkgName = unsafeDiscardStringContext (getField "Name:");
      pkgV    = unsafeDiscardStringContext (getField "Version:");
   in drvFromScript {
        inherit dir;
        name         = "nixFromCabal-${hsVer}-${pkgName}-${pkgV}";
        buildInputs  = [ haskellPackages.cabal2nix ];
      } ''
          source $stdenv/setup

          echo "Source is '$dir'" 1>&2
          cp -vr "$dir" ./source-"$name"
          pushd ./source-* > /dev/null

          echo "Setting permissions" 1>&2
          chmod +w . -R # We need this if dir has come from the store

          echo "Cleaning up unnecessary files" 1>&2
          rm -rf ".git" || true

          echo "Creating 'default.nix'" 1>&2
          touch default.nix
          chmod +w default.nix

          echo "Generating package definition" 1>&2
          cabal2nix ./. > default.nix
          echo "Finished generating" 1>&2
          popd > /dev/null

          echo "Adding to store" 1>&2
          cp -r ./source-* "$out"
        '';

nixFromCabal = dir: f:
let result = import (toString (nixedHsPkg dir f));

    # Support an "inner-composition" of "f" and "result", which behaves like
    # "args: f (result args)" but has explicit named arguments, to allow
    # "functionArgs" to work (as used by "callPackage").
    # TODO: Hopefully Nix will get a feature to set a function's argument names
    # Build a string "a,b,c" for the arguments of "result" which don't have
    # defaults
    resultArgs = functionArgs result;
    required   = filter (n: !resultArgs."${n}") (attrNames resultArgs);
    arglist    = lib.concatStrings (lib.intersperse "," required);

    # Strip the dependencies off our strings, so they can be embedded
    arglistF   = unsafeDiscardStringContext arglist;

    # Write a special-purpose composition function to a file, accepting the same
    # arguments ("arglistF") as "result".
    compose = toFile "cabal-compose.nix" ''
      f: g: args@{${arglistF}}: f (g args)
    '';
in

# If we've been given a function "f", compose it with "result" using our
# special-purpose function
if f == null then result
             else import compose f result;

}
