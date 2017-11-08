# Provides a set of Haskell packages for use by nix-eval.
{ hsDirs }:

# We use "./.." so that all of our dependencies get included
with import ../nix-support {};
with builtins;
with rec {
  hsDrvs  = self: listToAttrs (map (dir:
                    with { d = toString (nixedHsPkg dir); };
                    {
                      value = self.callPackage d {};
                      name  = pkgName (haskellPackages.callPackage d {}).name;
                    })
                    hsDirs);
  hsNames = attrNames (hsDrvs haskellPackages);
  givenHs = if getEnv("HASKELL_PACKAGES") == ""
               then haskellPackages
               else import getEnv("HASKELL_PACKAGES");
  hsPkgs  = givenHs.override {
    overrides = hsOverride (self: super: hsDrvs self);
  };

  # Check that these Haskell packages build
  check = runCommand "check-for-pkgs.nix"
    {
      buildInputs  = [((hsPkgs.ghcWithPackages (h: map (n: getAttr n h)
                                                       hsNames)).override {
                          ignoreCollisions = true;
                        })];
    }
    ''echo "true" > "$out"'';
};

assert hsDirs != [] || abort "Got no OUT_DIRS";
assert import check || abort "Couldn't build pkgs";
hsPkgs
