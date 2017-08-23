{ annotate, dumpToNix, haskellPackages, lib, nixedHsPkg, unpack }:

with builtins;
with lib;
with rec {

# Attach a bunch of intermediate results to test packages, so we can check
# and cache them

  extend = pkg: rec {
    inherit pkg;
    src  = nixedHsPkg (unpack pkg.src);

    dump = dumpToNix { pkgDir = src; };

    asts = annotate  {
      inherit pkg;
      asts   = dump;
      pkgSrc = src;
    };

    eqs = runCommand { inherit asts; buildInputs = [ package ]; } ''
      quickspecAsts > "$out"
    '';
  };
};
genAttrs [ "list-extras" ] (n: extend (getAttr n haskellPackages))
