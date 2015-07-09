#!/usr/bin/env bash

# Runs AstPlugin. Since we have dependencies available anyway, we also use GHCi
# to inspect types.
#
# This script makes the following assumptions:
#  - The current working directory contains a Cabal project
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg
#  - quickspec is also in the database of ghc-pkg

# All of these requirements can be satisfied by running in nix-shell

set -e

function typeCommand {
    echo ":m"
    echo ":set -XTemplateHaskell"
    #echo "import Language.Haskell.TH"
    while read -r LINE
    do
        QNAME=$(echo "$LINE" | jq -r '.module + "." + .name')
        mkQuery "$QNAME"
    done
}

function mkQuery {
    # Try to type-check QuickSpec signatures, to see which work
    # TODO: Higher-kinded morphism, eg. Functors and Monads

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
        # Format the current arity and the (qualified) name as JSON
        JSON="\"{\\\"arity\\\": $NUM, \\\"qname\\\": \\\"$1\\\"}\""

        # Pass f to QuickSpec, using our JSON as the identifier
        SIG="$QS.fun${NUM} ($JSON) f"

        # Extract the JSON from the signature
        EXPR="$QS.Term.name (head ($QS.Signature.symbols ($SIG)))"

        # Print out the JSON, so we can spot it when we parse the results
        echo "$BIND putStrLn ($EXPR)"
    done
}

function cabalLines {
    # Recombine any lines which GHCi split up
    while IFS= read -r LINE
    do
        if echo "$LINE" | grep '^ ' > /dev/null
        then
            printf  " ${LINE}"
        else
            printf "\n${LINE}"
        fi
    done
}

function pkgName {
    for CABAL in *.cabal
    do
        grep "name:" < "$CABAL" | grep -o ":.*" | grep -o "[^: ].*"
        return
    done
}

function getAsts {
    PKG=$(pkgName)
    build | grep "^{" | jq -c ". + {package: \"$PKG\"}"
}

function repl {
    cabal repl -v0 --ghc-options="-package quickspec -package QuickCheck -package template-haskell" |
        cabalLines
}

function build {
    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"
    # NOTE: GHC plugins write to stderr!
    cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null
}

ASTS=$(getAsts)
CMD=$(echo "$ASTS" | typeCommand)
RESULT=$(echo "$CMD" | repl)

# Output everything as JSON
jq -n --argfile asts   <(echo "$ASTS"   | jq -s    '.') \
      --argfile cmd    <(echo "$CMD"    | jq -s -R '.') \
      --argfile result <(echo "$RESULT" | jq -s -R '.') \
      '{asts: $asts, cmd: $cmd, result: $result}'
