{ bash, haskellPackages, jq, runScript, withDeps, writeScript }:

{ pkgSrc }:

with builtins;
let

# Recombines any lines which GHCi split up
replLines = writeScript "replLines" ''
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

# Run GHCi with all relevant packages available
repl = let cmd = "nix-shell --run 'ghci -v0 -XTemplateHaskell'";
           msg = "No default.nix found " + toJSON { inherit pkgSrc; };
           given = assert isString pkgSrc || typeOf pkgSrc == "path" ||
                          abort "runTypesScript: pkgSrc should be string or path, given ${typeOf pkgSrc}'";
                   assert isString (runScript { inherit pkgSrc; } ''
                            printf "%s" "$pkgSrc" > "$out"
                          '');
                   assert pathExists (unsafeDiscardStringContext "${pkgSrc}/default.nix") ||
                             abort "Couldn't find '${pkgSrc}/default.nix'";
                   ''(x.callPackage "${pkgSrc}" {})'';
           hsPkgs = "[x.QuickCheck x.quickspec x.hashable ${given}]";
        in writeScript "repl" ''
             ${cmd} -p "haskellPackages.ghcWithPackages (x: ${hsPkgs})"
           '';

# Writes GHCi commands to stdout, which we use to test the types of terms
typeCommand = writeScript "typeCommand" ''
                echo ":m"

                # Used for hashing values, to reduce memory usage.
                echo "import Data.Hashable"

                while read -r MOD
                do
                  echo "import $MOD"
                done < <(echo "$MODS")

                grep "^{" | while read -r LINE
                do
                  MOD=$(echo "$LINE" | "${jq}/bin/jq" -r '.module')
                  echo "import $MOD"
                  QNAME=$(echo "$LINE" | "${jq}/bin/jq" -r '.module + "." + .name')
                  "${mkQuery}" "$QNAME"
                done
              '';

# Try to type-check QuickSpec signatures, to see which work
# TODO: Higher-kinded polymorphism, eg. Functors and Monads
mkQuery = writeScript "mkQuery" ''
            # The name of the value we're trying to send through QuickSpec
            GIVEN="$1"

            # Shorthand
            QS="Test.QuickSpec"

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
            #    produced) they're hashed into an `Int` for storage and
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

              EXPR="$QS.Term.name (head ($QS.Signature.symbols ($1 ($JSON) f)))"

              # Print out the JSON, so we can spot it when we parse the results
              echo "$BIND putStrLn ($EXPR)"
            }

            # Try `blind` functions first; the higher the arity the better,
            # since outputting curried functions will likely prevent comparison.
            for NUM in 5 4 3 2 1 0
            do
              # We try calling our value as a function with $NUM arguments, then
              # send the result through `Data.Hashable.hash`.
              CALL="f"
              for ARG in $(seq 1 "$NUM")
              do
                CALL="$CALL undefined"
              done
              CALL="Data.Hashable.hash ($CALL)"

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

# Makes sure the types we've been given are actually available in scope (ie.
# they're not off in some hidden package)
typeScopes = writeScript "typeScopes" ''
               echo ":m"

               while read -r MOD
               do
                 echo "import $MOD"
               done < <(echo "$MODS")

               grep "in f[ ]*::" |
               while IFS= read -r LINE
               do
                 NAME=$(echo "$LINE" | sed -e "s/^.*('\(.*\)))[ ]*in f[ ]*::.*$/\1/g")
                 TYPE=$(echo "$LINE" | sed -e "s/^.*::[ ]*\(.*\)$/\1/g")
                 echo ":t ($NAME) :: ($TYPE)"
               done
             '';

# Makes sure that the modules we've been given can be imported.
checkMods = writeScript "checkMods" ''
  IMPORTS=$(echo "$MODS" |
            while read -r MOD
            do
              echo "import $MOD"
            done |
            ${repl} 2>&1)

  if echo "$IMPORTS" | grep "Could not find module"
  then
    exit 1
  fi
  exit 0
'';

in

# Runs GHCi to get type information
withDeps "runTypesScript" [ jq ] ''
  #!${bash}/bin/bash
  set -e

  ASTS=$(cat)

  MODS=$(echo "$ASTS" | jq -r '.[] | .module')
  export MODS

  echo "Checking module availability" 1>&2
  if "${checkMods}"
  then
    echo "Found modules" 1>&2
  else
    echo "Couldn't find modules, aborting" 1>&2
    exit 1
  fi

  ERR=$(mktemp "haskell-te-runTypesScript-XXXXX.stderr")
  echo '
    WARNING: We are about to gather information about Haskell definitions by
    trying a bunch of commands in GHCi and seeing what comes out. This will
    produce a bunch of messages beginning with "<interactive>"; this is
    perfectly normal behaviour, which you can ignore if everything else works.
    If you are experiencing problems elsewhere, some of these messages may be
    helpful.' > "$ERR"

  echo "Building type-extraction command" 1>&2
  CMD=$(echo "$ASTS" | jq -c '.[]' | "${typeCommand}") 2> "$ERR"

  echo "Extracting types" 1>&2
  RESULT=$(echo "$CMD" | "${repl}" | "${replLines}")

  echo "Building scope-checking command" 1>&2
  SCOPECMD=$(echo "$RESULT" | "${typeScopes}")

  echo "Checking scope" 1>&2
  SCOPERESULT=$(echo "$SCOPECMD" | "${repl}" | "${replLines}")

  echo '
    WARNING: This is the end of our GHCi abuse. Take heed of any GHC messages
    you see from this point on!' 1>&2

  echo "Outputting JSON" 1>&2
  # shellcheck disable=SC2016
  jq -n --argfile asts        <(echo "$ASTS")                       \
        --argfile cmd         <(echo "$CMD"         | jq -s -R '.') \
        --argfile result      <(echo "$RESULT"      | jq -s -R '.') \
        --argfile scopecmd    <(echo "$SCOPECMD"    | jq -s -R '.') \
        --argfile scoperesult <(echo "$SCOPERESULT" | jq -s -R '.') \
        '{asts: $asts, cmd: $cmd, result: $result, scopecmd: $scopecmd, scoperesult: $scoperesult}'
  echo "Finished output" 1>&2
''
