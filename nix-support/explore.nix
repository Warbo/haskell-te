{ benchmark, check, format, jq, lib, ml4hs, parseJSON,
  runScript, withNix, writeScript }:
with builtins;
with lib;

let

explore-theories = writeScript "explore-theories" ''
  function msg {
    echo -e "$*" 1>&2
  }

  if [[ "$#" -gt 0 ]]
  then
    msg "Reading clusters from '$1'"
    INPUT=$(cat "$1")
  elif ! [ -t 0 ]
  then
    msg "Reading clusters from stdin"
    INPUT=$(cat)
  else
    msg "Error: Please supply a filename or input to stdin"
    exit 1
  fi

  function pkgsFromInput {
    # Extracts packages as unquoted strings
    "${jq}/bin/jq" -r '.[] | .[] | .package'
  }

  function explore {
    PKGS=$(echo "$INPUT" | pkgsFromInput)
    echo "$INPUT" | ENVIRONMENT_PACKAGES="$PKGS" "${build-env}" "${path-to-front}" MLSpec "$@"
  }

  explore "$@"
'';

# Specify these once and only once
extra-haskell-packages = writeScript "extra-haskell-packages" ''
  cat <<EOF
  mlspec
  mlspec-helper
  runtime-arbitrary
  quickspec
  EOF
'';

extra-packages = writeScript "extra-packages" ''
printf mlspec
'';

path-to-front = writeScript "path-to-front" ''
  FST=$(echo "$PATH" | cut -d : -f1)
  if DIR=$(echo "$PATH" | grep -o -- "[^:]*$EXPLORE_NAME/[^:]*")
  then
    if ! [[ "x$FST" = "xDIR" ]]
    then
      echo "Pushing '$DIR' to front of PATH" 1>&2
      PATH="$DIR":"$PATH"
      export PATH
    fi
  fi

  echo "path-to-front: Running '$*'" 1>&2
  "$@"
'';

build-env = writeScript "build-env" ''
  # Run the command given in argv in an environment containing the Haskell
  # packages given on stdin
  BASE=$(dirname "$(readlink -f "$0")")

  function extraHaskellPackages {
    # Haskell packages required for MLSpec
    "${extra-haskell-packages}" | grep "^." | sed -e 's/^/h./g'
  }

  function extraPackages {
    "${extra-packages}"
  }

  function allExtras {
    printf "%s %s" "$(extraHaskellPackages)" "$(extraPackages)"
  }

  function mkGhcPkg {
    GIVEN=$(cat)
    printf "(haskellPackages.ghcWithPackages (h: [%s %s]))" "$GIVEN" "$(extraHaskellPackages)"
  }

  function mkName {
    GOT=$(cat)
    EXTRA=$(allExtras)
    UNIQUEID=$(echo "$GOT $EXTRA" | tr ' ' '\n' | sort -u | tr -d '[:space:]')
    MD5HASH=$(echo "$UNIQUEID" | md5sum | cut -d ' ' -f1)
    printf "explore-theories-%s" "$MD5HASH"
  }

  function mkEnvPkg {
    GHCPKG=$(mkGhcPkg)
    printf 'buildEnv { name = "%s"; paths = [%s %s];}' "$1" "$GHCPKG" "$(extraPackages)"
  }

  function haveHaskell {
    hash "ghc-pkg" > /dev/null 2>&1
  }

  function havePkg {
    ghc-pkg list "$1" | grep "$1" > /dev/null
  }

  function needEnv {
    # TODO: Doesn't take extraPackages into account yet
    haveHaskell || return 0

    while read -r PKG
    do
        havePkg "$PKG" || return 0
    done < <(extraHaskellPackages | cut -c 3-)

    NEEDED=$(cat)
    if [[ -n "$NEEDED" ]]
    then
        while read -r PKG
        do
            havePkg "$PKG" || return 0
        done < <(echo "$NEEDED")
    fi

    return 1
  }

  if [[ -z "$ENVIRONMENT_PACKAGES" ]]
  then
    # Sanity check
    if [[ -n "$ENVIRONMENT_PKGS" ]]
    then
      echo "WARNING: 'ENVIRONMENT_PKGS' was found; did you mean 'ENVIRONMENT_PACKAGES'?" 1>&2
      exit 1
    fi

    echo "No extra packages given" 1>&2
    INPUT=""
    HPKGS=""
  else
    echo "Extra packages given: $ENVIRONMENT_PACKAGES" 1>&2
    INPUT=$(echo "$ENVIRONMENT_PACKAGES" | sort -u | grep "^.")
    HPKGS=$(echo "$INPUT" | sed -e 's/^/h./')
  fi

    NAME=$(echo "$HPKGS" | mkName)
  ENVPKG=$(echo "$HPKGS" | mkEnvPkg "$NAME")

  if echo "$INPUT" | needEnv
  then
    echo "build-env: Running '$*' in Nix environment '$ENVPKG'" 1>&2
    EXPLORE_NAME="$NAME" nix-shell --show-trace --run "$*" -p "$ENVPKG"
  else
    echo "build-env: Running '$*' in existing environment" 1>&2
    "$@"
  fi
'';

explore = writeScript "format-and-explore" ''
            set -e
            function noDepth {
              grep -v "^Depth" || true # Don't abort if nothing found
            }
            "${explore-theories}" | noDepth
          '';

doExplore = quick: clusterCount: f:
              parseJSON (runScript {} ''
                set -e
                export CLUSTERS="${clusterCount}"
                "${benchmark quick "${explore}" []}" < "${f}" > "$out"
              '');

go = quick: clusterCount: clusters:
       map (doExplore quick clusterCount) clusters;

checkAndExplore = { quick, formatted }:
  let result = mapAttrs (go quick) formatted;
  in assert isAttrs formatted;
     assert all (n: isString n)                  (attrNames formatted);
     assert all (n: isInt (fromJSON n))          (attrNames formatted);
     assert all (n: isList formatted.${n})       (attrNames formatted);
     assert all (n: all isString formatted.${n}) (attrNames formatted);

     assert check "explored is set ${toJSON result}"
                  (isAttrs result);

     assert check "explored keys are numeric ${toJSON result}"
                  (all (n: isInt  (fromJSON n))  (attrNames result));

     assert check "explored values are lists ${toJSON result}"
                  (all (n: isList result.${n}) (attrNames result));

     assert check "explored values contain sets ${toJSON result}"
                  (all (n: all isAttrs result.${n}) (attrNames result));

     assert check "explored values have stdout ${toJSON result}"
                  (all (n: all (x: x ? stdout) result.${n})
                       (attrNames result));

     assert check "explored values have time ${toJSON result}"
                  (all (n: all (x: x ? time) result.${n})
                       (attrNames result));

     result;

in {
  inherit build-env;
  explore = checkAndExplore;
}
