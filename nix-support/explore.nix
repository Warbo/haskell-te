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

hsPkgsInEnv = env: names:
  let check = p: ''
        if ghc-pkg list "${p}" | grep "(no packages)" > /dev/null
        then
          echo "Package '${p}' not in generated environment" 1>&2
          exit 1
        fi
      '';
   in parseJSON (runScript env ''
        ${concatStringsSep "\n" (map check names)}
        echo "true" > "$out"
      '');

# Work out which packages we need, by reading JSON from 'f'. If 'standalone' is
# not null, use it as the path to a directory containing a Haskell package which
# we'll also include.
extractedEnv = standalone: f:
      # Use a variety of extra settings when 'standalone' is given
  let attrs   = if standalone != null &&
                   pathExists (unsafeDiscardStringContext
                                 "${toString standalone}/default.nix")
                   then trace "Including '${toString standalone}'" rec {
                     pkg   = haskellPackages.callPackage
                               (import standalone) {};
                     pkgs  = [ pkg      ];
                     names = [ pkg.name ];
                   }
                   else {
                     pkgs  = [];
                     names = [];
                   };
      hsNames = map strip (splitString "\n" (extractEnv f)) ++
                  extra-haskell-packages;
      hsPkgs  = h: (concatMap (n: if haskellPackages ? "${n}"
                                     then [ h."${n}" ]
                                     else [          ])
                              hsNames) ++ attrs.pkgs;
      extra   = map (n: self."${n}") extra-packages;
      ps      = [ (haskellPackages.ghcWithPackages hsPkgs) ] ++
                  extra;
   in assert hsPkgsInEnv { buildInputs = ps; } (hsNames ++ attrs.names);
      trace "Extracted env from '${f}'" ps;

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

doExplore = standalone: quick: clusterCount: f:
  let cmd    = toString (explore-theories f);
      script = ''
        set -e
        export CLUSTERS="${clusterCount}"
        "${benchmark {
             inherit quick cmd;
             inputs = [f];
         }}" < "${f}" > "$out"
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
  inherit extra-haskell-packages extra-packages explore-theories exploreEnv
          extractedEnv;
  explore = checkAndExplore;
}
