# A drop-in replacement for <nixpkgs>
# WATCH OUT! callPackage can introduce references to the underlying <nixpkgs>
# behind your back. If in doubt, pass arguments explicitly.
args:

let real = import <real> args; # <real> should point to the 'real' <nixpkgs>

    # If your <nixpkgs> is heavily customised, you can provide a pristine
    # version to use as 'original.pristine'
    original = if real ? pristine then real.pristine else real;

    # haskellPackages.override ensures dependencies are overridden too
    haskellPackages = import ./haskellPackages.nix {
                        inherit (original) haskellPackages;
                        nixFromCabal = import ./nixFromCabal.nix;
                      };

    overridden = original // original.callPackage ./defs.nix {
                               inherit real haskellPackages;
                             };
in overridden
