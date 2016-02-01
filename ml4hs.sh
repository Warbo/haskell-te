#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq bash cabal2db annotatedb
set -e

# Main ML4HS script

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

BASE=$(dirname "$0")

PACKAGE="${1}"
ARG="${PACKAGE}"

DIR="ML4HS.${PACKAGE}"
echo "Making temp dir '$DIR' for results"
mkdir -vp "$DIR"

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

#     COMMAND                            OUTPUT    INPUT
phase annotateDb                         deps      dump
phase "$BASE/extractFeatures.sh"         features  deps
phase "$BASE/nix_recurrentClustering.sh" clustered features

#echo "Running run-exploration.sh" >> /dev/stderr
#./run-exploration.sh < "$DIR/clustered"
