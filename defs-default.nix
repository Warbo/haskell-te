with import <nixpkgs> {}; with builtins; with lib;

# The core functionality offered by this package
callPackage ./defs.nix {
  cabal2db = (import ./shell.nix).override { doCheck = false; };
} // rec {

  # Useful helpers for testing

  strip = lib.removeSuffix ".nix";

  # Takes a directory D, returns { F = import D/F.nix; ... } for all F.nix in D
  importDir = dir:
    let addFile = x: old: old // builtins.listToAttrs [{
                                    name  = strip x;
                                    value = import (dir + "/${x}");
                                  }];
     in fold addFile {}
             (filter (hasSuffix ".nix")
                     (builtins.attrNames (builtins.readDir dir)));

  runScript = env: text: let hash   = unsafeDiscardStringContext (hashString "sha256" text);
                             script = writeScript "script-${hash}" text;
                             runner = runCommand  "runner-${hash}" env script;
                          in readFile "${runner}";

}
