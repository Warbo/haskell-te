#!/usr/bin/env bash
set -e

for CMD in dump-package annotateDb cluster jq
do
    command -v "$CMD" > /dev/null || {
        echo "ml4hs.sh requires $CMD" >> /dev/stderr
        exit 1
    }
done

# Main ML4HS script

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

[[ -n "$CLUSTERS" ]] || {
    echo "ML4HS needs the env var CLUSTERS to tell it how many clusters to use" >> /dev/stderr
    exit 1
}

PACKAGE="${1}"
ARG="${PACKAGE}"

if [[ -n "$ML4HSDIR" ]]
then
    [[ -d "$ML4HSDIR" ]] || {
        echo "Given directory '$ML4HSDIR' doesn't exist" >> /dev/stderr
        exit 1
    }
    DIR="$ML4HSDIR/${PACKAGE}"
else
    TEMPDIR=$(mktemp -d --tmpdir "ml4hs.${PACKAGE}.XXXXX")
    DIR="$TEMPDIR/${PACKAGE}"
    echo "Making temp dir '$DIR' for results"
fi

if [[ -d "$DIR" ]]
then
    echo "Directory '$DIR' already exists; leaving as-is" >> /dev/null
else
    mkdir -v "$DIR" >> /dev/stderr
fi

function phase {
    if [[ -e "$DIR/$2" ]]
    then
        echo "Found '$DIR/$2'" >> /dev/stderr
    else
        echo "Running '${1}' with '${ARG}'" >> /dev/stderr
        INPUT=""
        [[ -n "$3" ]] && INPUT=$(cat "${DIR}/${3}")
        echo "${INPUT}" | "${1}" "${ARG}" > "${DIR}/${2}" || {
            echo "Failed to run '${1}'" >> /dev/stderr
            exit 1
        }
    fi
}

# Provide a directory as PACKAGEDIR, or else we'll use Hackage
if [[ -z "${PACKAGEDIR}" ]]
then
    phase dump-hackage dump
else
    ARG="${PACKAGEDIR}"
    phase dump-package dump
    ARG="${PACKAGE}"
fi

BASE=$(dirname "$0")

#     COMMAND                       OUTPUT    INPUT
phase annotateDb                    asts      dump
phase cluster                       clustered asts
phase "$BASE/format-exploration.sh" formatted clustered

"$BASE/run-exploration.sh" < "$DIR/formatted"
