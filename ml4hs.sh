#! /usr/bin/env nix-shell
#! nix-shell -p jq -p bash -i bash
set -e

# Main ML4HS script

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

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
    phase ./dump-hackage.sh dump
else
    ARG="${PACKAGEDIR}"
    phase ./dump-package.sh dump
    ARG="${PACKAGE}"
fi

#     COMMAND                      OUTPUT    INPUT
phase ./runTypes.sh                types     dump
phase ./annotateAsts.sh            asts      types
phase ./getDeps.sh                 deps      asts

#./findMissing.sh < "$DIR/deps" | sort -u | tee "$DIR/missing" >> /dev/stderr

phase ./extractFeatures.sh         features  deps
phase ./nix_recurrentClustering.sh clustered features

#echo "Running run-exploration.sh" >> /dev/stderr
#./run-exploration.sh < "$DIR/clustered"
