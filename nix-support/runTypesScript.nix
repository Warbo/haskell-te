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
           hsPkgs = "[x.QuickCheck x.quickspec ${given}]";
        in writeScript "repl" ''
             ${cmd} -p "haskellPackages.ghcWithPackages (x: ${hsPkgs})"
           '';

typeCommand = writeScript "typeCommand" ''
                echo ":m"

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
            # Shorthand
            QS="Test.QuickSpec"

            # Use Template Haskell to monomorphise our function (tries to
            # instantiate all type variables with "Integer")
            MONO="Test.QuickCheck.All.monomorphic ('$1)"

            # We must use a layer of let/in for TH to work, so we call our
            # monomorphic function "f"
            BIND="let f = \$($MONO) in"

            # Get the monomorphised type
            echo ":t $BIND f"

            # Try turning our monomorphised function into a QuickSpec Sig(nature)
            for NUM in 5 4 3 2 1 0
            do
              # Format the current arity and the (qualified) name as JSON. If this
              # works, this term is 'quickspecable' (i.e. suitable for use in a
              # QuickSpec signature)
              JSON="\"{\\\"arity\\\": $NUM, \\\"qname\\\": \\\"$1\\\", \\\"quickspecable\\\": true}\""

              # Pass f to QuickSpec, using our JSON as the identifier
              SIG="$QS.fun$NUM ($JSON) f"

              # Extract the JSON from the signature
              EXPR="$QS.Term.name (head ($QS.Signature.symbols ($SIG)))"

              # Print out the JSON, so we can spot it when we parse the results
              echo "$BIND putStrLn ($EXPR)"
          done
        '';

# Make sure the types we've been given are actually available in scope (ie.
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
