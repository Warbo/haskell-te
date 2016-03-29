{ stdenv, haskellPackages }:
assert haskellPackages ? quickspec;
assert haskellPackages ? QuickCheck;
assert haskellPackages ? AstPlugin;

pkgDir: pkgName:
assert haskellPackages ? "${pkgName}";

let hash = builtins.hashString "sha256" pkgDir;
in stdenv.mkDerivation {
  inherit pkgDir;
  name        = "build-package-${pkgName}";
  buildInputs = [
    haskellPackages.cabal-install

    (haskellPackages.ghcWithPackages (hsPkgs: [
      hsPkgs.quickspec  # For `fun0`, `fun1`, etc.
      hsPkgs.QuickCheck # For `monomorphise`
      hsPkgs.${pkgName} # For dependencies
      hsPkgs.AstPlugin  # For AST extraction
    ]))
  ];

  # Copy the pkgDir to the store and try to build it
  builder = builtins.toFile "build-package-builder" ''
    source "$stdenv/setup"
    cp -rv "$pkgDir" ./pkgDir
    chmod +w -R ./pkgDir
    cd pkgDir

    mkdir -p "$out"

    export HOME="$TMPDIR"
    if cabal configure && cabal build
    then
      echo 0 > "$out/buildable"
    else
      echo 1 > "$out/buildable"
    fi
  '';
}
