{ benchmark, ourCheck, self, format, haskellPackages, jq, lib, ml4hs, parseJSON,
  runScript, writeScript }:
with builtins;
with lib;

let

explore-theories = f: writeScript "explore-theories" ''
  set -e
  set -o pipefail

  INPUT=$(cat)

  function noDepth {
    grep -v "^Depth" || true # Don't abort if nothing found
  }

  # Extracts packages as unquoted strings
  ENVIRONMENT_PACKAGES="${extractEnv f}"
  export ENVIRONMENT_PACKAGES

  echo "$INPUT" | MLSpec "$@" | noDepth | jq -s '.'
'';

extractEnv = f:
  runScript { buildInputs = [ jq ]; } ''
    set -e
    set -o pipefail

    [[ -e "${f}" ]] || {
      echo "Path '${f}' doesn't exist" 1>&2
      exit 1
    }

    jq -r '.[] | (if type == "array" then .[] else . end) | .package' < "${f}" |
      sort -u > "$out"
  '';

extractedEnv = standalone: f:
  let strip  = s: let unpre = removePrefix "\n" (removePrefix " " s);
                      unsuf = removeSuffix "\n" (removeSuffix " " unpre);
                   in if unsuf == s
                         then s
                         else strip unsuf;
      extra     = standalone != null;
      salonePkg = haskellPackages.callPackage (import standalone) {};
      salone    = if pathExists "${toString standalone}/default.nix"
                     then trace "Including extra package ${toString standalone}"
                            [ salonePkg ]
                     else trace "Ignoring ${toString standalone} with no default.nix"
                            [];
      custom = map strip (splitString "\n" (extractEnv f));
      hsPkgs = custom ++ extra-haskell-packages;
      areHs  = filter (n: haskellPackages ? "${n}") hsPkgs;
      hs     = haskellPackages.ghcWithPackages (h:
                 (map (n: h."${n}") areHs) ++ (if extra
                                                  then salone
                                                  else []));
      ps     = [ hs ] ++ (map (n: self."${n}") extra-packages);
      msg    = if extra
                  then "including '${toString standalone}'"
                  else "";
      checkPkg = p: ''
          if ghc-pkg list "${p}" | grep "(no packages)" > /dev/null
          then
            echo "Package '${p}' not in generated environment" 1>&2
            exit 1
          fi
        '';
      doCheck  = parseJSON (runScript { buildInputs = ps; } ''
                 ${if extra
                      then checkPkg salonePkg.name
                      else ""}
                 echo "true" > "$out"
               '');
   in trace "Extracted env from '${f}' ${msg}"
            (assert doCheck; ps);

# Haskell packages required for MLSpec
extra-haskell-packages = [ "mlspec" "mlspec-helper" "runtime-arbitrary"
                           "quickspec" ];

prefixed-haskell-packages = concatStringsSep "\n"
                              (map (x: "h.${x}") extra-haskell-packages);

extra-packages = [ "jq" "mlspec" ];

exploreEnv = [ (haskellPackages.ghcWithPackages (h: map (n: h."${n}")
                                                    extra-haskell-packages)) ] ++
             (map (n: self."${n}") extra-packages);

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

  echo "]))"
'';

# Run the command given in argv in an environment containing the Haskell
# packages given on stdin
build-env = writeScript "build-env" ''
  #!/usr/bin/env bash
  set -e
  set -o pipefail

  function ensurePkg {
    if ghc-pkg list "$1" | grep "$1" > /dev/null
    then
      return 0
    fi

    GHC_PKG=$(command -v ghc-pkg)
    PKGS=$(ghc-pkg list)
    echo    "Didn't find Haskell package '$1' with '$GHC_PKG'." 1>&2
    echo -e "Available packages are:\n$PKGS\n\nAborting" 1>&2
    exit 1
  }

  function ensureEnv {
    # TODO: Doesn't take extraPackages into account yet
    hash "ghc-pkg" > /dev/null 2>&1 || {
      echo "Need environment to get the ghc-pkg command" 1>&2
      exit 1
    }

    while read -r PKG
    do
        ensurePkg "$PKG"
    done < <(echo "${concatStringsSep "\n" extra-haskell-packages}")

    NEEDED=$(cat)
    if [[ -n "$NEEDED" ]]
    then
        while read -r PKG
        do
            ensurePkg "$PKG"
        done < <(echo "$NEEDED")
    fi

    return 0
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
  else
    echo "Extra packages given: $ENVIRONMENT_PACKAGES" 1>&2
    INPUT=$(echo "$ENVIRONMENT_PACKAGES" | sort -u | grep "^.")
  fi

  echo "$INPUT" | ensureEnv

  "$@"
'';

doExplore = standalone: quick: clusterCount: f:
  let cmd    = toString (explore-theories f);
      script = ''
        set -e
        export CLUSTERS="${clusterCount}"
        "${benchmark quick cmd []}" < "${f}" > "$out"
      '';
      env    = { buildInputs = extractedEnv standalone f; };
   in parseJSON (runScript env script);

go = { quick, standalone }: clusterCount: clusters:
       map (doExplore standalone quick clusterCount) clusters;

aCheck = formatted: result:
  assert isAttrs formatted;
  assert all (n: isString n)                  (attrNames formatted);
  assert all (n: isInt (fromJSON n))          (attrNames formatted);
  assert all (n: isList formatted."${n}")       (attrNames formatted);
  assert all (n: all isString formatted."${n}") (attrNames formatted);

  assert ourCheck "explored is set ${toJSON result}"
               (isAttrs result);

  assert ourCheck "explored keys are numeric ${toJSON result}"
               (all (n: isInt  (fromJSON n))  (attrNames result));

  assert ourCheck "explored values are lists ${toJSON result}"
               (all (n: isList result."${n}") (attrNames result));

  assert ourCheck "explored values contain sets ${toJSON result}"
               (all (n: all isAttrs result."${n}") (attrNames result));

  assert ourCheck "explored values have stdout ${toJSON result}"
               (all (n: all (x: x ? stdout) result."${n}")
                    (attrNames result));

  assert ourCheck "explored values have time ${toJSON result}"
               (all (n: all (x: x ? time) result."${n}")
                    (attrNames result));
  true;

checkAndExplore = { quick, formatted, standalone ? null }:
  let results = mapAttrs (go { inherit quick standalone; }) formatted;
      failed  = any (n: any (x: x.failed) results."${n}") (attrNames results);
      result  = { inherit results failed; };
   in if failed then result
                else assert aCheck formatted result.results; result;

in {
  inherit build-env extra-haskell-packages extra-packages explore-theories
          exploreEnv extractedEnv;
  explore = checkAndExplore;
}
