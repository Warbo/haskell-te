# Import useful stuff
let pkgs = import ./. {};
 in with pkgs; with builtins; with lib;

# Import all *.nix files from ./tests, pass pkgs to each and collect up the
# resulting tests
let tests       = import ./tests.nix { inherit pkgs; };
    testResults = mapAttrs (n: t: dbug "Running test '${n}'" t)
                           tests;

    flatten     = t: if isBool t
                        then [ (testMsg t "Unknown") ]
                        else if t ? type && t.type == "derivation"
                                then [ t ]
                                else concatMap flatten (attrValues t);

    result      = flatten testResults;
 in testWrap result "All tests passed"
