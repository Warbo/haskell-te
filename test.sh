#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

function msg {
    echo "$1" >> /dev/stderr
}

function fail {
    msg "FAIL: $1"
    exit 1
}

function noDupes {
    DUPES=$(grep "^building path.*repo-head" |
            sed -e 's/.*head-//g'            |
            sort                             |
            uniq -D)
    [[ -z "$DUPES" ]] || fail "Made redundant package lookups: $DUPES"
}

function explore {
    "$BASE/explore-theories" < "$1" 2>&1
}

function testNoDupes {
    echo "Making sure packages aren't checked over and over" >> /dev/stderr
    for F in data/*
    do
        echo "Exploring '$F'" >> /dev/stderr
        OUTPUT=$(explore "$F") || fail "Failed to explore '$F'"
        echo "$OUTPUT" | noDupes
    done
    echo "No duplicate checks were spotted" >> /dev/stderr
}

function testExplorationFindsEquations {
    echo "Making sure exploration actually works" >> /dev/stderr
    FOUND=0
    for F in data/*
    do
        echo "Exploring '$F'" >> /dev/stderr
        OUTPUT=$(explore "$F") || fail "Failed to explore '$F': $OUTPUT"

        echo "$OUTPUT" | grep "No clusters found" &&
            fail "No clusters found by MLSpec (did it receive any input?)"

        if echo "$OUTPUT" | grep "^{" > /dev/null
        then
            msg "Found equations for '$F'"
            FOUND=1
        else
            msg "Couldn't find any equations in output of '$F':\n$OUTPUT"
        fi
    done

    if [[ "$FOUND" -eq 0 ]]
    then
        fail "No equations found from files in data/"
    else
        msg "Exploration worked, found some equations from data/"
    fi
}

function testNoRegressions {
    OUTPUT=$(explore data/hastily.formatted.1) ||
        fail "Failed to explore 'hastily':\n$OUTPUT"
}

function testEmptyEnv {
    # The contents of extra-haskell-packages should be available, even with no
    # ENVIRONMENT_PACKAGES given
    while read -r PKG
    do
        unset ENVIRONMENT_PACKAGES
        "$BASE/build-env" ghc-pkg list "$PKG" ||
            fail "Extra package '$PKG' wasn't found with empty environment"
    done < <("$BASE/extra-haskell-packages")
}

function testEnvContainsPkgs {
    # Append more and more Haskell packages to ENVIRONMENT_PACKAGES
    PKGS=""
    for NEWPKG in text containers parsec aeson
    do
        PKGS=$(echo -e "$PKGS\n$NEWPKG")

        # For each package we're giving to build-env, check it becomes available
        # by calling ghc-pkg
        for PKG in $PKGS
        do
            OUTPUT=$(ENVIRONMENT_PACKAGES="$PKGS" "$BASE/build-env" ghc-pkg list "$PKG") ||
                fail "Couldn't run ghc-pkg in build-env for '$PKG' in '$PKGS'"
            echo "$OUTPUT" | grep "$PKG" > /dev/null ||
                fail "Didn't find package '$PKG' in ghc-pkg output '$OUTPUT'"
            echo "Package '$PKG' was found in the environment" >> /dev/stderr
        done
    done
}

function nixception {
    # For use by testEnvIsNotRedundant. Requires particular variables to be
    # initialised. We only keep it separate to avoid heredoc annoyances.
    # shellcheck disable=SC2086
    nix-shell --show-trace -p "$GHCPKG" $EXTRA --run bash <<EOF
      echo "BEGIN INNER SHELL" >> /dev/stderr
      for PKG in $HLINE
      do
          ENVIRONMENT_PACKAGES="$EXTRAH" "$BASE/build-env" ghc-pkg list "\$PKG" |
               grep "\$PKG" > /dev/null || {
              echo "Didn't find '\$PKG' in environment" >> /dev/stderr
              exit 1
          }
      done
EOF
}

function testEnvIsNotRedundant {
    msg "Checking we don't build a new nix-shell when packages are available"

    # build-env adds some 'extra' packages on to those we give it; they must be
    # available too
    EXTRA=$("$BASE/extra-packages")
    EXTRAH=$("$BASE/extra-haskell-packages" | grep "^.")
    HLINE=$(echo "$EXTRAH" | tr '\n' ' ')
    PREFIXED=$(echo "$EXTRAH"| sed -e 's/^/h./g')
    GHCPKG="haskellPackages.ghcWithPackages (h: [$PREFIXED])"

    msg "Building an environment for each Haskell package, inside a nix-shell"
    msg "which already has them all available"
    OUTPUT=$(nixception 2>&1) || fail "Inner environment is missing packages"

    msg "Making sure build-env ran"
    echo "$OUTPUT" | grep "BEGIN INNER SHELL" > /dev/null ||
        fail "Inner shell didn't seem to run"

    msg "Making sure build-env didn't create a new Nix environment"
    echo "$OUTPUT" | grep -A 9999 "BEGIN INNER SHELL" | grep "building path" &&
        fail "Built Nix environment when it wasn't needed"

    msg "build-env didn't make unnecessary environment"
}

testEmptyEnv
testEnvContainsPkgs
testEnvIsNotRedundant
testExplorationFindsEquations
testNoDupes
testNoRegressions

echo "Tests passed (check prior output for more information)"
