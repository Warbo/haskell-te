with import <nixpkgs> {};
name:
  runCommand "dummy" {
    buildInputs = [
      jq
      haskellPackages.cabal-install
      (haskellPackages.ghcWithPackages (hsPkgs: [
        hsPkgs.quickspec  # For `fun0`, `fun1`, etc.
        hsPkgs.QuickCheck # For `monomorphise`
        hsPkgs.${name}    # For dependencies
        hsPkgs.AstPlugin  # For AST extraction
      ]))
    ];
  } ""
