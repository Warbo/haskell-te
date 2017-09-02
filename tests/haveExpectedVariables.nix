defs: with defs;

with rec {
  runner = runCommand "list-full-runner"
    (withNix {
      asts        = testData.asts.list-full;
      OUT_DIR     = nixify testData.haskellPkgs.list-full;
      buildInputs = [ genQuickspecRunner ];
    })
    ''
      R=$(genQuickspecRunner < "$asts")
      ln -s "$R" "$out"
    '';

  env = runCommand "list-full-env" { inherit runner; } ''
    grep -v '^exec ' < "$runner" > "$out"
  '';

  code = runCommand "code.hs"
    {
      inherit env;
      buildInputs = [ fail ];
    }
    ''
      source "$env"
      [[ -e "$HASKELL_CODE" ]] || fail "HASKELL_CODE ($HASKELL_CODE) not found"
      ln -s "$HASKELL_CODE" "$out"
    '';

  countVars = with { ticks = "''"; }; writeScript "countVars.hs" ''
    -- TODO: We don't need all of these
    import Test.QuickSpec hiding (lists)
    import Test.QuickSpec.Signature
    import Data.Digest.Murmur32
    import Data.Serialize
    import MLSpec.Helper
    import A
    import IfCxt
    import Test.QuickCheck
    import Test.RuntimeArbitrary
    import Prelude
    import GHC.Types
    import qualified Test.Feat as F

    mkIfCxtInstances ${ticks}F.Enumerable
    mkIfCxtInstances ${ticks}Ord
    mkIfCxtInstances ${ticks}CoArbitrary
    mkIfCxtInstances ${ticks}Arbitrary

    func1 = ("Unary",   Test.RuntimeArbitrary.getArbGen
                          [Prelude.undefined :: ((->) Prelude.Integer
                                                      Prelude.Integer)])
    func2 = ("Binary",  Test.RuntimeArbitrary.getArbGen
                          [Prelude.undefined :: ((->) Prelude.Integer
                                                      ((->) Prelude.Integer
                                                            Prelude.Integer))])
    ints  = ("Integer", Test.RuntimeArbitrary.getArbGen
                          [Prelude.undefined :: (Prelude.Integer)])
    lists = ("List",    Test.RuntimeArbitrary.getArbGen
                          [Prelude.undefined :: ((A.List) Prelude.Integer)])
    nats  = ("Nat",     Test.RuntimeArbitrary.getArbGen
                          [Prelude.undefined :: (A.Nat)])

    check (t, l) = case l of
      [] -> error ("No Arbitrary instance for " ++ t)
      _  -> return ()

    main = sequence [
        check ints
      , check nats
      , check lists
      , check func1
      , check func2
      , putStrLn "Found Arbitrary instances"
      ]
  '';
};
{
  askForVariables = runCommand "ask-for-vars" { inherit code; } ''
    echo "Ensuring Haskell code requests variables for appropriate types" 1>&2

    # Find where we're adding variables to the signature and get their types
    # This parsing is pretty fragile; if it breaks, it might be worth using
    # haskell-src-exts or similar.
    TYPES=$(grep -A 2 'MLSpec.Helper.addVars' < "$code" |
            grep 'getArbGen'                            |
            grep -o ':: .*\]'                           |
            grep -o ' .*[^]]'                           |
            grep -o '[^ ].*[^ ]'                        )

    for TYPE in Prelude.Integer '(A.List) Prelude.Integer'
    do
      echo "$TYPES" | grep -F "$TYPE" > /dev/null || {
        echo "Didn't ask for variables of type '$TYPE'" 1>&2
        exit 1
      }
    done

    echo "pass" > "$out"
  '';

  haveGenerators = runCommand "have-generators"
    {
      inherit countVars env;
      buildInputs = [ genQuickspecRunner ];
    }
    ''
      set -e
      echo "Checking that we can find Arbitrary instances" 1>&2
      source "$env"
      $CMD < "$countVars"
      echo "pass" > "$out"
    '';
}
