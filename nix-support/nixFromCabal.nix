{ haskellPackages, lib, stdenv }:
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

assert typeOf dir == "path" || isString dir;
assert f == null || isFunction f;

let hsVer   = haskellPackages.ghc.version;
    cabalF  = head (filter (x: hasSuffix ".cabal" x) (attrNames (readDir dir)));
    cabalC  = map (replaceStrings [" " "\t"] ["" ""])
                  (splitString "\n" (readFile (dir + "/${cabalF}")));
    pkgName = replaceStrings ["name:"] [""]
                             (head (filter (hasPrefix "name:") cabalC));
    pkgV    = replaceStrings ["version:"] [""]
                             (head (filter (hasPrefix "version:") cabalC));
    nixed   = stdenv.mkDerivation {
      inherit dir;
      name         = "nixFromCabal-${hsVer}-${pkgName}-${pkgV}";
      buildInputs  = [ haskellPackages.cabal2nix ];
      buildCommand = ''
        source $stdenv/setup

        echo "Copying '$dir' to '$out'"
        cp -vr "$dir" "$out"
        cd "$out"

        echo "Setting permissions"
        chmod +w . # We need this if dir has come from the store

        echo "Cleaning up unnecessary files"
        rm -rf ".git" || true

        echo "Creating '$out/default.nix'"
        touch default.nix
        chmod +w default.nix

        echo "Generating package definition"
        cabal2nix ./. > default.nix
        echo "Finished generating"
      '';
    };
    result = import "${nixed}";

    # Support an "inner-composition" of "f" and "result", which behaves like
    # "args: f (result args)" but has explicit named arguments, to allow
    # "functionArgs" to work (as used by "callPackage").
    # TODO: Hopefully Nix will get a feature to set a function's argument names
    # Build a string "a,b,c" for the arguments of "result" which don't have
    # defaults
    resultArgs = functionArgs result;
    required   = filter (n: !resultArgs.${n}) (attrNames resultArgs);
    arglist    = lib.concatStrings (lib.intersperse "," required);

    # Strip the dependencies off our strings, so they can be embedded
    arglistF   = unsafeDiscardStringContext arglist;
    nixedF     = unsafeDiscardStringContext nixed;

    # Write a special-purpose composition function to a file, accepting the same
    # arguments ("arglistF") as "result".
    compose = toFile "cabal-compose.nix" ''
      f: g: args@{${arglistF}}: f (g args)
    '';
in

# If we've been given a function "f", compose it with "result" using our
# special-purpose function
if f == null then result
             else import compose f result
