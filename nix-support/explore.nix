{ benchmark, check, format, jq, lib, ml4hs, parseJSON,
  runScript, writeScript }:
with builtins;
with lib;

let

explore-theories = writeScript "explore-theories" ''
  set -e
  set -o pipefail

  INPUT=$(cat)

  # Extracts packages as unquoted strings
  ENVIRONMENT_PACKAGES=$(echo "$INPUT" | "${jq}/bin/jq" -r '.[] | .package' | sort -u)
  export ENVIRONMENT_PACKAGES

  echo "$INPUT" | "${build-env}" MLSpec "$@"
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

extra-packages = [ "mlspec" ];

mkGhcPkg = writeScript "mkGhcPkg" ''
  set -e
  set -o pipefail

  echo "(haskellPackages.ghcWithPackages (h: ["

  GIVEN=($1)
  EXTRA=($2)
  for PKG in "''${GIVEN[@]}" "''${EXTRA[@]}"
  do
    UNQUAL=$(echo "$PKG" | sed -e 's/^h\.//g')
    FOUND=$(nix-instantiate --eval -E \
            "let pkgs = import <nixpkgs> {}; in pkgs.haskellPackages ? $UNQUAL")
    if [[ "x$FOUND" = "xtrue" ]]
    then
      echo "$PKG"
    else
      echo "Couldn't find '$PKG' in haskellPackages; ignoring, in the hope we have a nixFromCabal alternative" 1>&2
    fi
  done

  echo "$STANDALONE_PKG" # Possibly empty, but allows non-Hackage packages

  echo "]))"
'';

build-env = writeScript "build-env" ''
  #!/usr/bin/env bash
  set -e
  set -o pipefail

  # Run the command given in argv in an environment containing the Haskell
  # packages given on stdin

  function extraHaskellPackages {
    # Haskell packages required for MLSpec
    "${extra-haskell-packages}" | grep "^." | sed -e 's/^/h./g'
  }

  function mkEnvPkg {
    GIVEN=$(cat)
    GHCPKG=$("${mkGhcPkg}" "$GIVEN" "$(extraHaskellPackages)")
    printf 'buildEnv { name = "%s"; paths = [%s %s];}' \
                              "$1"          "$GHCPKG"  \
                                            "${concatStringsSep " " extra-packages}"
  }

  function havePkg {
    ghc-pkg list "$1" | grep "$1" > /dev/null
  }

  function needEnv {
    # TODO: Doesn't take extraPackages into account yet
    hash "ghc-pkg" > /dev/null 2>&1 || return 0

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

  function mkName {
    GOT=$(cat)
    EXTRA=$(printf "%s %s" "$(extraHaskellPackages)" "${concatStringsSep " " extra-packages}")
    MD5HASH=$(echo "$GOT $EXTRA" | tr ' ' '\n' | sort -u | tr -d '[:space:]' | md5sum | cut -d ' ' -f1)
    printf "explore-theories-%s" "$MD5HASH"
  }

    NAME=$(echo "$HPKGS" | mkName)
  ENVPKG=$(echo "$HPKGS" | mkEnvPkg "$NAME")

  if echo "$INPUT" | needEnv
  then
    echo "build-env: Running '$*' in Nix environment '$ENVPKG'" 1>&2
    nix-shell --show-trace --run "$*" -p "$ENVPKG"
  else
    echo "build-env: Running '$*' in existing environment" 1>&2
    "$@"
  fi
'';

withStandalonePkg = src: ''export STANDALONE_PKG="${standalonePkg src}"'';

standalonePkg = src: ''(haskellPackages.callPackage (import ${src} ) {})'';

explore = writeScript "format-and-explore" ''
            set -e
            set -o pipefail

            function noDepth {
              grep -v "^Depth" || true # Don't abort if nothing found
            }
            "${explore-theories}" | noDepth
          '';

doExplore = standalone: quick: clusterCount: f:
              parseJSON (runScript {} ''
                set -e
                export CLUSTERS="${clusterCount}"
                ${if standalone == null
                                then ""
                                else withStandalonePkg standalone}
                "${benchmark quick (toString explore) []}" < "${f}" > "$out"
              '');

go = { quick, standalone }: clusterCount: clusters:
       map (doExplore standalone quick clusterCount) clusters;

doCheck = formatted: result:
  assert isAttrs formatted;
  assert all (n: isString n)                  (attrNames formatted);
  assert all (n: isInt (fromJSON n))          (attrNames formatted);
  assert all (n: isList formatted."${n}")       (attrNames formatted);
  assert all (n: all isString formatted."${n}") (attrNames formatted);

  assert check "explored is set ${toJSON result}"
               (isAttrs result);

  assert check "explored keys are numeric ${toJSON result}"
               (all (n: isInt  (fromJSON n))  (attrNames result));

  assert check "explored values are lists ${toJSON result}"
               (all (n: isList result."${n}") (attrNames result));

  assert check "explored values contain sets ${toJSON result}"
               (all (n: all isAttrs result."${n}") (attrNames result));

  assert check "explored values have stdout ${toJSON result}"
               (all (n: all (x: x ? stdout) result."${n}")
                    (attrNames result));

  assert check "explored values have time ${toJSON result}"
               (all (n: all (x: x ? time) result."${n}")
                    (attrNames result));
  true;

checkAndExplore = { quick, formatted, standalone ? null }:
  let results = mapAttrs (go { inherit quick standalone; }) formatted;
      failed  = any (n: any (x: x.failed) results."${n}") (attrNames results);
      result  = { inherit results failed; };
   in if failed then result
                else assert doCheck formatted result.results; result;

in {
  inherit build-env extra-haskell-packages extra-packages explore-theories
          exploration-env;
  explore = checkAndExplore;
}
