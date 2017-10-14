{ bash, bashEscape, checkStderr, fail, gnugrep, gnused, haskellPackages,
  haskellPkgNameVersion, haveVar, jq, makeWrapper, mkBin, nix, nixEnv, nixify,
  pipeToNix, runCommand, testData, timeout, withDeps, withNix, wrap,
  writeScript }:

with rec {
  getCmd = wrap {
    name   = "getCmd";
    paths  = [
      bash jq nix
      (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
    ];
    vars   = nixEnv // {
      code = writeScript "getCmd.hs" ''
        {-# LANGUAGE OverloadedStrings #-}
        import           Data.Aeson
        import qualified Data.ByteString.Lazy.Char8 as BS
        import           MLSpec.Theory
        import           Language.Eval.Internal

        render ts x = "main = do { eqs <- quickSpecAndSimplify (" ++
                        withoutUndef' (renderWithVariables x ts)  ++
                        "); mapM_ print eqs; }"

        -- Reads JSON from stdin, outputs a QuickSpec signature and associated
        -- shell and Nix commands for running it
        main = do
          projects <- getProjects <$> getContents
          let t = case projects of
                       [t] -> t
                       _   -> let l = show (length projects)
                               in error ("Got " ++ l ++ " projects")

          rendered <- renderTheory t
          let (ts, x) = case rendered of
                             Just (ts, x) -> (ts, x)
                             Nothing      -> let msg = "Failed to render "
                                              in error (msg ++ show t)

          BS.putStrLn (encode (object [
              "runner" .= unwords ("runhaskell" : flagsOf x),
              "env"    .= pkgOf x,
              "code"   .= buildInput (render ts) x
            ]))
      '';
    };
    script = ''
      #!/usr/bin/env bash
      jq 'map(select(.quickspecable))' | runhaskell "$code"
    '';
  };

  keepJson  = mkBin {
    name   = "keepJson";
    paths  = [ bash gnugrep jq ];
    script = ''
      #!/usr/bin/env bash
      set -e

      # Strip out cruft that QuickSpec puts on stdout. Since this is just a
      # filter, we don't actually care if grep finds anything or not; hence
      # we use '|| true' to avoid signalling an error
      function strip {
        grep -v '^Depth' || true
      }

      strip | jq -s '.'
    '';
  };

  runner = wrap {
    name   = "quickspecRunner";
    paths  = [ bash checkStderr haveVar keepJson timeout ];
    vars   = { NIX_EVAL_HASKELL_PKGS = toString ./quickspecEnv.nix; };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar CMD
      haveVar HASKELL_CODE
      haveVar PKG_NAME
      haveVar NIX_EVAL_HASKELL_PKGS
      haveVar OUT_DIR

      function run {
        # Let users choose time/memory limits by wrapping in withTimout
        withTimeout $CMD 2> >(checkStderr)
      }

      run < "$HASKELL_CODE" | keepJson
    '';
  };

  generateCode = mkBin {
    name   = "genQuickspecRunner";
    paths  = [
      (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
      fail haskellPkgNameVersion haveVar jq nix pipeToNix
    ];
    vars   = nixEnv // {
      inherit getCmd runner;
      NIX_EVAL_HASKELL_PKGS = builtins.toString ./quickspecEnv.nix;
      mkCmd = writeScript "quickspec-builder.nix" ''
        with builtins;
        assert getEnv "NIXENV"   != "" || abort "No NIXENV set";
        assert getEnv "OUT_DIR"  != "" || abort "No OUT_DIR set";
        assert getEnv "PKG_NAME" != "" || abort "No PKG_NAME set";
        assert getEnv "CMD"      != "" || abort "No CMD set";
        (import ${toString ../nix-support} {}).wrap {
          name  = "quickspec-runner";
          paths = [ (import (toFile "env.nix" (getEnv "NIXENV"))) ];
          vars  = {
            CMD          = getEnv("CMD");
            HASKELL_CODE = getEnv("HASKELL_CODE");
            OUT_DIR      = getEnv("OUT_DIR");
            PKG_NAME     = getEnv("PKG_NAME");
          };
          file  = getEnv("runner");
        }
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar OUT_DIR

      PKG_NAME=$(haskellPkgNameVersion "$OUT_DIR" | jq -r '.package')
      export PKG_NAME

      ALL=$(cat)
       QS=$(echo "$ALL" | jq 'map(select(.quickspecable))')

      echo "$QS" | jq -e 'length | . > 0' > /dev/null ||
        fail "Nothing quickspecable ($QS) in ($ALL)"

      # Get the required environment, code and Haskell command
      GENERATED=$(echo "$QS" | "$getCmd") || {
        echo -e "Given:\n$ALL\n" 1>&2
        echo -e "Chosen:\n$QS\n" 1>&2
        fail "Couldn't generate QuickSpec code"
      }
      [[ -n "$GENERATED" ]] || fail "Empty GENERATED"

      # Store code in a file since it may be too big for an env var
      HASKELL_CODE=$(echo "$GENERATED" | jq -r '.code'  | pipeToNix "qsCode.hs")
            NIXENV=$(echo "$GENERATED" | jq -r '.env'   )
               CMD=$(echo "$GENERATED" | jq -r '.runner')

      export  HASKELL_CODE
      haveVar HASKELL_CODE
      export  NIXENV
      haveVar NIXENV
      export  CMD
      haveVar CMD

      # Encapsulate the command and code into a standalone script
      nix-build --no-out-link --show-trace -E 'import (builtins.getEnv "mkCmd")'
    '';
  };

  tests = rec {
    runner = runCommand "list-full-runner"
      (withNix {
        asts        = (testData.asts {}).list-full;
        OUT_DIR     = nixify (testData.haskellPkgs {}).list-full;
        buildInputs = [ generateCode ];
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

    askForVariables = runCommand "ask-for-vars"
      {
        inherit code;
        buildInputs = [ fail ];
      }
      ''
        set -e
        echo "Checking Haskell code requests vars for appropriate types" 1>&2

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
          echo "$TYPES" | grep -F "$TYPE" > /dev/null ||
            fail "Didn't ask for variables of type '$TYPE'"
        done

        echo "pass" > "$out"
      '';

    haveGenerators = runCommand "have-generators"
      {
        inherit countVars env;
        buildInputs = [ generateCode ];
      }
      ''
        set -e
        echo "Checking that we can find Arbitrary instances" 1>&2
        source "$env"
        $CMD < "$countVars"
        echo "pass" > "$out"
      '';
  };
};
withDeps [ tests.askForVariables tests.haveGenerators ] generateCode
