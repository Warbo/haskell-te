with builtins;
with { ourPkgs = import ./. {}; };
with ourPkgs;
with lib;
with rec {
  testResults = import ./tests.nix { pkgs = ourPkgs; };

  flatten     = path: t:
    if isBool t
       then [ (testMsg t (toJSON path)) ]
       else if t ? type && t.type == "derivation"
               then [ t ]
               else [ (testWrap (attrValues
                        (mapAttrs
                          (n: v: testWrap (flatten (path ++ [ n ]) v)
                                          (toJSON  (path ++ [ n ])))
                        t))
                        (toJSON path)) ];
};

testWrap (flatten [ "tests" ] testResults) "All tests passed"
