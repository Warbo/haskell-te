{ benchmark, ourCheck, self, format, haskellPackages, jq, lib, ml4hs, parseJSON,
  runScript, strip, writeScript }:
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
  let attrs     = if standalone != null &&
                     pathExists (unsafeDiscardStringContext
                                   "${toString standalone}/default.nix")
                     then {
                       hs      = [ salonePkg ];
                       msg     = "including '${toString standalone}'";
                       doCheck = check salonePkg.name;
                     }
                     else {
                       hs      = [];
                       msg     = "";
                       doCheck = "";
                     };
      salonePkg = haskellPackages.callPackage (import standalone) {};
      hsPkgs    = map strip (splitString "\n" (extractEnv f)) ++
                  extra-haskell-packages;
      hs        = h: map (n: h."${n}")
                         (filter (n: haskellPackages ? "${n}")
                                 hsPkgs);
      ps        = trace "FIXME: Check each Haskell package is in env" ([ (haskellPackages.ghcWithPackages (hs ++ attrs.hs)) ] ++
                  (map (n: self."${n}") extra-packages));
      check     = p: ''
                       if ghc-pkg list "${salonePkg.name}" | grep "(no packages)" > /dev/null
                       then
                         echo "Package '${salonePkg.name}' not in generated environment" 1>&2
                         exit 1
                       fi
                     ''
      doCheck   = parseJSON (runScript { buildInputs = ps; } ''
                    ${attrs.doCheck}
                    echo "true" > "$out"
                  '');
   in trace "Extracted env from '${f}' ${attrs.msg}"
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

  exit 0
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
