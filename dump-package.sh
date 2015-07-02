#!/bin/sh

# Extract ASTs from the Cabal package in the current directory

function packageName {
    (shopt -s nullglob
     for CBL in *.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

function extractAsts {
    PKG=$(packageName)
    nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
              --run "sh" <<'EOF'
# Get this shell's Haskell package database. The first line of `ghc-pkg list`
# will tell us, except for a pesky ':' at the end of the line
GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')

# Tell GHC to use the right package database, to expose the AstPlugin package,
# and to run the AstPlugin.Plugin during compilation
PLUGIN="AstPlugin.Plugin"
OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=$PLUGIN"

# Build the project, passing the above options through to GHC.
# NOTE: AstPlugin writes to stderr, not stdout, so we redirect it (blame GHC!)
export COLUMNS=640000  # Should be enough for anyone ;)
UNTYPED=$(cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null)

# Whilst we have all the dependencies available, we can try getting the types
# too. This will encounter errors, eg. for non-exported names, but that's a
# feature: if we can't use them from here, then QuickSpec can't later on either!
# TODO: In the future, we might try looping through all of the executables, test
# suites, etc. to make sure we cover everything.
ASTS=$(echo "$UNTYPED" |
           while read RAWLINE
           do
               # See if we're dealing with an AST or something else
               if echo "$RAWLINE" | grep "^FOUNDAST " > /dev/null
               then
                   # Skip explicit dictionary-passing
                   if echo "$RAWLINE" | grep '\.\$' > /dev/null
                   then
                       true
                   else
                       # Trim off the "FOUNDAST " prefix
                       echo "$RAWLINE" | cut -d ' ' -f 2-
                   fi
               else
                 # Since these lines came from stderr, we might as well
                 # report them
                 echo "$RAWLINE" > /dev/stderr
               fi
           done)

# Build one big type-printing command, to avoid GHCi setup/teardown overhead
# The ":m" unloads everything except Prelude, ensuring that names all get
# qualified and we can't see any non-exported members
CMD=$(echo ":m";
      echo "$ASTS" |
           while read LINE
           do
               # Extract the name
               NAME=$(echo "$LINE" | cut -d ' ' -f 1 |
                                     cut -d ':' -f 2)
               # Make a GHCi command to print the type
               echo ":t (${NAME})"
           done)

# Run the command through GHCi and concatenate any responses which spill over
# multiple lines
RESPONSE=$(echo "$CMD" | cabal repl |
               while read LINE
               do
                  if echo "$LINE" | grep '^Prelude>' > /dev/null
                  then
                      printf "\n${LINE}"
                  else
                      printf " ${LINE}"
                  fi
               done)

# Extract any types we were given
TYPES=$(echo "$RESPONSE" |
            while read LINE
            do
                echo "$LINE" | cut -d '>' -f 2- | grep " :: "
            done)

# Print out all ASTs which have a corresponding type (quadratically slowly!)
echo "$ASTS" | while read LINE
               do
                   NAME=$(echo "$LINE" | cut -d ' ' -f 1)
                   AST=$(echo "$LINE" | cut -d ' ' -f 2-)
                   QNAME=$(echo "$NAME" | cut -d ':' -f 2-)
                   TYPE=$(echo "$TYPES" | grep "(${QNAME}) ::" |
                              grep -o ": .*" |
                              grep -o "[^ :].*")
                   if [ -n "$TYPE" ]
                   then
                       echo "${NAME}:\"${TYPE}\" ${AST}"
                   fi
               done
EOF
}

function fixPackageName {
    # FIXME: This is a hack. AstPlugin should get the package name and include
    # it in the output, but we seem to get "(unknown):Foo.bar (ast)".
    # The easy workaround is to replace "(unknown)" with the given package name.
    # Longer-term, it would be better to fix this in AstPlugin itself.
    PKG=$(packageName)
    cut -d ':' -f 2- | while read LINE
                       do
                           echo "$PKG:$LINE"
                       done
}

extractAsts | fixPackageName
