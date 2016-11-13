{ haskellPackages, jq, runScript, writeScript }: { pkg, pkgSrc }:
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
           msg = "No default.nix found " + toJSON {
                   inherit pkgSrc;
                   inherit (pkg) name;
                   srcNixed = if pkg ? srcNixed
                                 then { inherit (pkg) srcNixed; }
                                 else {};
                 };
           given = if pkgSrc == null
                      then if haskellPackages ? "${pkg.name}"
                              then "x.${pkg.name}"
                              else abort "haskellPackages doesn't contain '${pkg.name}'"
                      else assert isString (runScript { inherit pkgSrc; } ''
                                    printf "%s" "$pkgSrc" > "$out"
                                  '');
                           if pathExists (unsafeDiscardStringContext "${pkgSrc}/default.nix")
                              then ''(x.callPackage "${pkgSrc}" {})''
                              else if pkg ? srcNixed &&
                                      pathExists "${pkg.srcNixed}/default.nix"
                                      then ''(x.callPackage "${pkg.srcNixed}" {})''
                                      else abort msg;
           hsPkgs = "[x.QuickCheck x.quickspec ${given}]";
        in writeScript "repl" ''
             ${cmd} -p "haskellPackages.ghcWithPackages (x: ${hsPkgs})"
           '';

typeCommand = writeScript "typeCommand" ''
                echo ":m"
                grep "^{" | while read -r LINE
                do
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
               grep "in f[ ]*::" |
               while IFS= read -r LINE
               do
                 NAME=$(echo "$LINE" | sed -e "s/^.*('\(.*\)))[ ]*in f[ ]*::.*$/\1/g")
                 TYPE=$(echo "$LINE" | sed -e "s/^.*::[ ]*\(.*\)$/\1/g")
                 echo ":t ($NAME) :: ($TYPE)"
               done
             '';

in

# Runs GHCi to get type information
writeScript "runTypes" ''
  #!/usr/bin/env bash
  set -e

  function jq {
    "${jq}/bin/jq" "$@"
  }

  ASTS=$(cat)

  echo "Building type-extraction command" 1>&2
  CMD=$(echo "$ASTS" | jq -c '.[]' | "${typeCommand}")

  echo "Extracting types" 1>&2
  RESULT=$(echo "$CMD" | "${repl}" | "${replLines}")

  echo "Building scope-checking command" 1>&2
  SCOPECMD=$(echo "$RESULT" | "${typeScopes}")

  echo "Checking scope" 1>&2
  SCOPERESULT=$(echo "$SCOPECMD" | "${repl}" | "${replLines}")

  echo "Outputting JSON" 1>&2
  # shellcheck disable=SC2016
  jq -n --argfile asts        <(echo "$ASTS")                       \
        --argfile cmd         <(echo "$CMD"         | jq -s -R '.') \
        --argfile result      <(echo "$RESULT"      | jq -s -R '.') \
        --argfile scopecmd    <(echo "$SCOPECMD"    | jq -s -R '.') \
        --argfile scoperesult <(echo "$SCOPERESULT" | jq -s -R '.') \
        '{asts: $asts, cmd: $cmd, result: $result, scopecmd: $scopecmd, scoperesult: $scoperesult}'
''
