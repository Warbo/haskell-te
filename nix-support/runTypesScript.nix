{ bash, fail, haskellPackages, jq, lib, mkBin, nixEnv, withNix, wrap,
  writeScript }:

with builtins;
with lib;
with rec {
  # Run GHCi with all relevant packages available. We need "--pure" to avoid
  # multiple GHCs appearing in $PATH, since we may end up calling one with the
  # wrong package database.
  repl = mkBin {
    name  = "repl";
    paths = (withNix {}).buildInputs ++ [ replLines ];
    vars  = nixEnv // {
      cmd = "ghci -v0 -XTemplateHaskell";
      pkg =
        with {
          hs     = "with builtins; haskellPackages.ghcWithPackages";
          hsPkgs = "x.QuickCheck x.quickspec x.cereal x.murmur-hash";
        };
        ''
          ${hs} (x: [ ${hsPkgs} (x.callPackage (getEnv "pkgSrc") {}) ])
        '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail
      nix-shell --show-trace --pure -p "$pkg" --run "$cmd" | replLines
    '';
  };

  # Makes sure that the modules we've been given can be imported.
  checkMods = mkBin {
    name   = "checkMods";
    paths  = [ repl ];
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      ALL_MODS=$(echo -e "$MODS\nData.Serialize\nData.Digest.Murmur32")
       IMPORTS=$(echo "$ALL_MODS" |
                 while read -r MOD
                 do
                   echo "import $MOD"
                 done |
                 repl 2>&1)

      if echo "$IMPORTS" | grep "Could not find module"
      then
        exit 1
      fi
      exit 0
    '';
  };

  # Try to type-check QuickSpec signatures, to see which work
  # TODO: Higher-kinded polymorphism, eg. Functors and Monads
  mkQuery = mkBin {
    name   = "mkQuery";
    vars   = {
      # Shorthand
      QS = "Test.QuickSpec";

      # Make sure our parens stay balanced!
      FUNCS = concatStringsSep " " [
         "Data.Digest.Murmur32.asWord32"
        "(Data.Digest.Murmur32.hash32"
        "(Data.Serialize.runPut"
        "(Data.Serialize.put"
      ];
    };
    script = ''
      #!/usr/bin/env bash
      # The name of the value we're trying to send through QuickSpec
      GIVEN="$1"

      # Use Template Haskell to monomorphise our value (tries to
      # instantiate all type variables with "Integer")
      MONO="Test.QuickCheck.All.monomorphic ('$1)"

      # We must use a layer of let/in for TH to work, so we call our
      # monomorphic value "f"
      BIND="let f = \$($MONO) in"

      # Get the monomorphised type
      echo ":t $BIND f"

      # See if our monomorphised value can be added to a QuickSpec
      # Sig(nature). This can be done in two ways:
      #
      #  - Directly, using `fun0`, `fun1`, `fun2`, etc. depending on the
      #    arity. This requires the type (or result type, for functions)
      #    be an instance of `Ord`. Values of this type will be compared
      #    to discover equivalence classes; such values can build up on
      #    the heap, causing memory exhaustion.
      #  - Indirectly, by adding our value using one of the `blind0`,
      #    `blind1`, etc. functions (depending on arity) which don't
      #    compare (or store) their outputs. We then add a hash function
      #    to the signature using `observer1`; whenever our function
      #    generates an output (or any other value of that type is
      #    produced) they're hashed into an `Word32` for storage and
      #    comparison.
      #
      # We prefer the indirect method, to keep down memory usage.

      function tryCall() {
        # Try to make a QuickSpec signature using the given parameters,
        # writing JSON to stdout on success.
        #  - $1 is the function to call, an arbitrarily complex expression
        #  - $2 is the arity we'll report in our JSON
        #  - $3 is whether results are hashable (indirect) or not

        # Construct the JSON we'll send to stdout. This is double-escaped:
        #  - We need to use "" in the shell to splice in variables
        #  - We're generating Haskell code, which uses "" for strings
        #  - The Haskell string contains JSON, which uses "" for strings
        # We include the given name, the given arity and whether it's
        # hashable. We can assume it's quickspecable, since the message
        # won't appear if it isn't.
         QNAME="\\\"qname\\\": \\\"$GIVEN\\\""
        FIELDS="$QNAME, \\\"quickspecable\\\": true"
          JSON="\"{\\\"arity\\\": $NUM, \\\"hashable\\\":$3, $FIELDS}\""

        # We use the given function to add our term (monomorphised as `f`)
        # to a QuickSpec signature; we use the above JSON as its name. We
        # extract this name and print it out; if this works, then the term
        # must be suitable for use in QuickSpec.

        EXPR="$QS.Term.name (Prelude.head ($QS.Signature.symbols ($1 ($JSON) f)))"

        # Print out the JSON, so we can spot it when we parse the results
        echo "$BIND Prelude.putStrLn ($EXPR)"
      }

      # Try `blind` functions first; the higher the arity the better,
      # since outputting curried functions will likely prevent comparison.
      for NUM in 5 4 3 2 1 0
      do
        # We try calling our value as a function with $NUM arguments, then
        # send the result through cereal and murmur-hash.
        CALL="f"
        for ARG in $(seq 1 "$NUM")
        do
          CALL="$CALL Prelude.undefined"
        done
        CALL="($FUNCS ($CALL)))))"

        # We don't need the result of the hash call, so we put it in an
        # unused let/in variable; the result we want is a call to `blind`
        tryCall "let g = $CALL in $QS.blind$NUM" "$NUM" true
      done

      # If we can't hash, try adding directly (requires output be `Ord`)
      for NUM in 5 4 3 2 1 0
      do
        # Try constructing a signature using `fun5`, `fun4`, etc. until
        # we either get a success, or run out (not QuickSpecable).
        tryCall "$QS.fun$NUM" "$NUM" false
      done
    '';
  };

  # Writes GHCi commands to stdout, which we use to test the types of terms
  typeCommand = mkBin {
    name   = "typeCommand";
    paths  = [ jq mkQuery ];
    script = ''
      echo ":m"

      # Used for hashing values, to reduce memory usage.
      echo "import qualified Data.Serialize"
      echo "import qualified Data.Digest.Murmur32"

      while read -r MOD
      do
        echo "import qualified $MOD"
      done < <(echo "$MODS")

      grep "^{" | while read -r LINE
      do
        MOD=$(echo "$LINE" | jq -r '.module')
        echo "import qualified $MOD"
        QNAME=$(echo "$LINE" | jq -r '.module + "." + .name')
        mkQuery "$QNAME"
      done
    '';
  };

  # Makes sure the types we've been given are actually available in scope (ie.
  # they're not off in some hidden package)
  typeScopes = mkBin {
    name   = "typeScopes";
    script = ''
      echo ":m"

      while read -r MOD
      do
        echo "import qualified $MOD"
      done < <(echo "$MODS")

      grep "in f[ ]*::" |
      while IFS= read -r LINE
      do
        NAME=$(echo "$LINE" | sed -e "s/^.*('\(.*\)))[ ]*in f[ ]*::.*$/\1/g")
        TYPE=$(echo "$LINE" | sed -e "s/^.*::[ ]*\(.*\)$/\1/g")
        echo ":t ($NAME) :: ($TYPE)"
      done
    '';
  };

  # Recombines any lines which GHCi split up
  replLines = mkBin {
    name   = "replLines";
    script = ''
      #!/usr/bin/env bash
      while IFS= read -r LINE
      do
        if echo "$LINE" | grep '^ ' > /dev/null
        then
          printf  " %s" "$LINE"
        else
          printf "\n%s" "$LINE"
        fi
      done
    '';
  };
};

# Runs GHCi to get type information
rec {
  script = wrap {
    name   = "runTypesScript-raw";
    paths  = [ bash checkMods fail jq repl typeCommand typeScopes ];
    vars   = {
      JQ_COMMAND = concatStrings [
        "{"
          (concatStringsSep ", "
            (map (x: x + ": $" + x)
                 [ "asts" "cmd" "result" "scopecmd" "scoperesult" ]))
        "}"
      ];
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      ERR=$(mktemp "/tmp/haskell-te-runTypesScript-XXXXX.stderr")

      function finish {
        cat "$ERR" 1>&2
        rm -f "$ERR"
      }
      trap finish EXIT

      ASTS=$(cat)

      MODS=$(echo "$ASTS" | jq -r '.[] | .module')
      export MODS

      echo "Checking module availability" 1>&2
      if checkMods
      then
        echo "Found modules" 1>&2
      else
        fail "Couldn't find modules, aborting"
      fi

      echo "Building type-extraction command" 1>&2
      CMD=$(echo "$ASTS" | jq -c '.[]' | typeCommand) 2> "$ERR" ||
        fail "Error building type extraction command"

      echo "Extracting types" 1>&2
      RESULT=$(echo "$CMD" | repl 2>> "$ERR") ||
        fail "Error extracting types"

      echo "Building scope-checking command" 1>&2
      SCOPECMD=$(echo "$RESULT" | typeScopes)

      echo "Checking scope" 1>&2
      SCOPERESULT=$(echo "$SCOPECMD" | repl)

      echo "Outputting JSON" 1>&2
      # shellcheck disable=SC2016
      jq -n --argfile asts        <(echo "$ASTS")                       \
            --argfile cmd         <(echo "$CMD"         | jq -s -R '.') \
            --argfile result      <(echo "$RESULT"      | jq -s -R '.') \
            --argfile scopecmd    <(echo "$SCOPECMD"    | jq -s -R '.') \
            --argfile scoperesult <(echo "$SCOPERESULT" | jq -s -R '.') \
            "$JQ_COMMAND"
      echo "Finished output" 1>&2

      if [[ -z "$IN_SELF_TEST" ]]
      then
        if [[ "$DEBUG" -eq 1 ]]
        then
          {
            echo 'DEBUG detected, showing stderr output'
            echo 'NOTE: This comes from trial-and-error in GHCi, so we expect'
            echo "many error messages. They can aid debugging, but if you aren't"
            echo 'experiencing a problem then they can be safely ignored.'
            cat "$ERR"
          } 1>&2
        else
          echo "Set DEBUG=1 if you want to see gory GHCi output." 1>&2
        fi
      fi
      echo "" > "$ERR"
    '';
  };

  runTypesScript = { pkgSrc }: wrap {
    name = "runTypesScript";
    file = script;
    vars = { inherit pkgSrc; };
  };
}
