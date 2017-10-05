{ cabal2nix, lib, runCommand }:

with builtins;
with lib;
dir:
  assert typeOf dir == "path" || isString dir || isDerivation dir ||
         abort "nixedHsPkg: dir should be str|path|drv, given '${typeOf dir}'";
  runCommand "nixedHsPkg"
    {
      inherit dir;
      name         = "nixFromCabal";
      buildInputs  = [ cabal2nix ];
    }
    ''
      source $stdenv/setup

      echo "Source is '$dir'" 1>&2
      cp -r "$dir" ./source-"$name"
      pushd ./source-* > /dev/null
        echo "Setting permissions" 1>&2
        chmod +w . -R # We need this if dir has come from the Nix store
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
    ''
