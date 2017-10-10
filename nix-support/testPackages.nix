{ annotated, cluster, dumpToNix, haskellPackages, lib, nixedHsPkg, package,
  runCommand, unpack }:

with builtins;
with lib;
with rec {

# Attach a bunch of intermediate results to test packages, so we can check
# and cache them

  extend = pkg: rec {
    inherit pkg;
    inherit (pkg) name;

    src  = nixedHsPkg (unpack pkg.src);

    dump = dumpToNix { pkgDir = src; };

    asts = annotated { pkgDir = unpack pkg.src; };

    eqs = runCommand "eqs-of-${name}"
      {
        inherit asts;
        buildInputs = [ package ];
        OUT_DIR     = src;
      }
      ''
        quickspecAsts < "$asts" > "$out"
      '';

    clustered = runCommand "cluster" { inherit asts cluster; } ''
      "$cluster" < "$asts" > "$out"
    '';
  };
};
genAttrs [ "list-extras" ] (n: extend (getAttr n haskellPackages))
